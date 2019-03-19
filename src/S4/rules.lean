import .semantics
open nnf subtype list

-- inductive node (Γ : sseqt) : Type
-- | closed : unsatisfiable (Γ.m ++ Γ.b) → node
-- | open_ : Π m : model, (minfo m.val).Γ = Γ → node

inductive node (Γ : sseqt) : Type
| closed : unsatisfiable (Γ.m ++ Γ.b) → node
| open_ : {x : model // (minfo x.1).Γ = Γ}  → node

open node

def contra_rule_seqt {Δ : sseqt} {n} (h : var n ∈ Δ.m ∧ neg n ∈ Δ.m) : node Δ := 
begin
  left,
  {exact unsat_contra_seqt h.1 h.2}
end

def and_rule_seqt {Γ Δ : sseqt} (i : and_instance_seqt Γ Δ) : node Δ → node Γ
| (closed h) := begin 
                  left, 
                  {apply unsat_of_closed_and_seqt, repeat {assumption}}, 
                end
| (open_ w)  := 
begin
right,
swap,
clear and_rule_seqt,
cases i with φ ψ h,
cases w with w pw,
cases w with wt pwa,
cases wt with iw lw sgw,
let rhtk := and φ ψ :: iw.htk,
have hhtk : hintikka rhtk,
  {split, 
   {intros n hn, cases hn, 
    {contradiction}, 
    {intro hne, cases hne, contradiction, 
     apply iw.hhtk.hno_contra, exact hn, exact hne} },
   {intros φ' ψ' h, cases h with heq hmem, 
    {injection heq with eq₁ eq₂, 
     rw eq₁,
     right,
     apply iw.mhtk,
     simp at pw,
     rw pw, simp},
    {right, 
     apply iw.hhtk.hand_left, exact hmem} },
   {intros φ' ψ' h, cases h with heq hmem, 
    {injection heq with eq₁ eq₂, 
     rw eq₂,
     right,
     apply iw.mhtk,
     simp at pw,
     rw pw, simp},
    {right,
     apply iw.hhtk.hand_right, exact hmem}},
   {intros φ' ψ' h, cases h with heq hmem,
    {contradiction},
    {have := iw.hhtk.hor hmem, cases this,
     {left, right, exact this}, 
     {right, right, exact this}}},
   {intros φ' h, cases h with heq hmem,
    {contradiction},
    {right, apply iw.hhtk.hbox, exact hmem}}},
have mhtk : Γ.m ⊆ rhtk,
  {intros x hx, by_cases heq : x = and φ ψ, 
   {rw heq, simp}, 
   {have : x ∈ iw.Γ.m, 
     {simp at pw, rw pw, dsimp, right, right, 
      have := (mem_erase_of_ne heq).2 hx, exact this},
    right, apply iw.mhtk this }},
let im : info := ⟨Γ, rhtk, hhtk, mhtk⟩,  
let tm : tmodel := tmodel.cons im lw sgw,
have ptm : ptmodel tm, 
  {split,
   {simp, have := pwa.1.bhist, simp at pw, simp at this, rw pw at this, simp at this, exact this},
   {simp, have := pwa.1.sbox, simp at this, exact this},
   {simp, have := pwa.1.pdia, simp at this, exact this},
   {simp, have := pwa.1.bdia, simp at pw, simp at this, 
    rw pw at this, simp at this, 
    intros s rq hdesc hmem, rw eq_desc_of_eq_children at hdesc, swap, exact iw, swap, exact sgw,
    have := this s rq hdesc hmem, 
    cases this with hl hr, 
    {left, exact hl}, 
    {right, rcases hr with ⟨d, hd⟩, rw eq_desc_of_eq_children at hd, split, exact hd} },
   {simp, have := pwa.1.reqb, simp at pw, simp at this, rw pw at this, simp at this, exact this},
   {simp, have := pwa.1.sreq, simp at pw, simp at this, rw pw at this, simp at this, exact this}},
have gpt : global_pt tm, 
  {intros s hs, have := pwa.2 s, rw eq_desc_of_eq_children at this, apply this, exact hs},
have hinfo : (minfo tm).Γ = Γ, {simp},
exact ⟨⟨tm, ⟨ptm, gpt⟩⟩, hinfo⟩
end

inductive batch_eq : list model → list sseqt → Prop
| bs_nil : batch_eq [] []
| bs_cons (m:model) (Γ:sseqt) (l₁ l₂) : (minfo m.1).Γ = Γ → 
                                        batch_eq l₁ l₂ → 
                                        batch_eq (m::l₁) (Γ::l₂)

open batch_eq

theorem be_ex : Π l Γ, 
batch_eq l Γ → ∀ (m : model), m ∈ l → ∃ i ∈ Γ, (minfo m.1).Γ = i
| l Γ bs_nil := λ m hm, by simpa using hm
| l Γ (bs_cons m Δ l₁ l₂ h hbs) := 
begin
  intros n hn, 
  cases hn,
  {split, swap, exact Δ, split, simp, rw hn, exact h},
  {have : ∃ (i : sseqt) (H : i ∈ l₂), (minfo (n.val)).Γ = i,
     {apply be_ex, exact hbs, exact hn},
   rcases this with ⟨w, hw, hsat⟩, split, swap, exact w, split, 
   {simp [hw]}, {exact hsat}}
end

theorem be_forall : Π l Γ, 
batch_eq l Γ → ∀ i ∈ Γ, ∃ (m : model) (h : m ∈ l), (minfo m.1).Γ = i
| l Γ bs_nil := λ m hm, by simpa using hm
| l Γ (bs_cons m Δ l₁ l₂ h hbs) := 
begin
  intros i hi,
  cases hi, {split, swap, exact m, split, simp, rw hi, exact h},
  {have : ∃ (n : model) (H : n ∈ l₁), (minfo (n.val)).Γ = i,
     {apply be_forall, exact hbs, exact hi},
   rcases this with ⟨w, hw, hsat⟩, split, swap, exact w, split, 
   {simp [hw]}, {exact hsat} }
end

theorem mem_be_box : Π l Γ, 
batch_eq l (unmodal_seqt Γ) → ∀ (m : model), m ∈l → ∀ φ, box φ ∈ Γ.b → box φ ∈ htk m.1 := 
begin
  intros l Γ hbs m hm φ hφ,
  have := be_ex _ _ hbs _ hm,
  rcases this with ⟨i,hin,hi⟩,
  have := unmodal_mem_box _ _ hin φ hφ,
  rw ←hi at this,
  cases m with m pm,
  cases m with im lm sgm,
  simp, simp at this,
  apply im.mhtk this
end

theorem mem_be_dia : Π l Γ, 
batch_eq l (unmodal_seqt Γ) → ∀ φ, dia φ ∈ Γ.m → φ ∉ Γ.h →
∃ (i : model) (h : i ∈ l), φ ∈ htk i.1 :=
begin
  intros l Γ hbs φ h₁ h₂,
  have := mem_unmodal_seqt _ _ ⟨h₂, h₁⟩,
  rcases this with ⟨w, hmem, hw⟩,
  have := be_forall _ _ hbs w hmem,
  rcases this with ⟨m, hm, heq⟩,
  split, split, exact hm,
  cases m with m pm,
  cases m with im lm sgm,
  rw ←heq at hw, simp, simp at hw,
  apply im.mhtk hw
end

def dia_rule_seqt {p : sseqt → Prop} (f : Π Γ, p Γ → node Γ): Π Γ : list sseqt, (∀ i∈Γ, p i) → 
psum ({i // i ∈ Γ ∧ unsatisfiable (sseqt.m i ++ sseqt.b i)}) 
{x : list model // batch_eq x Γ}
| [] h := psum.inr ⟨[], bs_nil⟩
| (hd :: tl) h := 
match f hd (h hd (by simp)) with
| (node.closed pr) := psum.inl ⟨hd, by simp, pr⟩
| (node.open_ w₁) := 
  match dia_rule_seqt tl (λ x hx, h x $ by simp [hx]) with
  | (psum.inl uw) := begin 
                       left, rcases uw with ⟨w, hin, h⟩, 
                       split, split, swap, exact h, simp [hin]
                     end
  | (psum.inr w₂) := psum.inr ⟨(w₁.1::w₂), bs_cons _ _ _ _ w₁.2 w₂.2⟩
  end
end

@[simp] def dia_rule_loop (h b : list nnf) : list nnf → list psig
| [] := []
| (dia φ::tl) := if φ ∈ h then ⟨φ, b⟩ :: dia_rule_loop tl else dia_rule_loop tl
| (e::tl) := dia_rule_loop tl

theorem mem_loop_left : Π h b m φ (h₁ : φ ∈ h) (h₂ : dia φ ∈ m),
(⟨φ, b⟩ : psig) ∈ dia_rule_loop h b m
| h b [] φ h₁ h₂ := absurd h₂ $ list.not_mem_nil _
| h b (hd :: tl) φ h₁ h₂ := 
begin
cases h' : hd,
case nnf.dia : ψ 
{simp, by_cases hc : ψ ∈ h,
 {rw if_pos, cases h₂, 
  {rw h' at h₂, injection h₂ with heq, left, rw heq},
  {right, apply mem_loop_left, exact h₁, exact h₂}, exact hc },
 {rw if_neg, cases h₂, {rw h' at h₂, injection h₂ with heq, rw heq at h₁, contradiction}, {apply mem_loop_left, exact h₁, exact h₂},
 exact hc}},
all_goals 
{simp, rw h' at h₂, cases h₂, contradiction, apply mem_loop_left, repeat {assumption}}
end

theorem mem_loop_right_aux : Π h b m φ, (⟨φ, b⟩ : psig) ∈ dia_rule_loop h b m → dia φ ∈ m 
| h b [] φ h₁ := absurd h₁ $ list.not_mem_nil _
| h b (hd :: tl) φ h₁ := 
begin
cases h₂ : hd,
case nnf.dia : ψ 
{rw h₂ at h₁, dsimp at h₁, 
 by_cases hc : ψ ∈ h, 
 {rw if_pos at h₁, cases h₁, {simp at h₁, rw h₁, simp}, {have := mem_loop_right_aux h b tl φ h₁, right, exact this},exact hc},
 {rw if_neg at h₁, have := mem_loop_right_aux h b tl φ h₁, right, exact this, exact hc} },
all_goals 
{rw h₂ at h₁, simp at h₁, right, apply mem_loop_right_aux, exact h₁}
end

theorem mem_loop_right : Π h b m φ, (⟨φ, b⟩ : psig) ∈ dia_rule_loop h b m → φ ∈ h 
| h b [] φ h₁ := absurd h₁ $ list.not_mem_nil _
| h b (hd :: tl) φ h₁ := 
begin
cases h₂ : hd,
case nnf.dia : ψ 
{rw h₂ at h₁, dsimp at h₁, 
 by_cases hc : ψ ∈ h, 
 {rw if_pos at h₁, cases h₁, {simp at h₁, rw h₁, exact hc}, {have := mem_loop_right h b tl φ h₁, exact this},exact hc},
 {rw if_neg at h₁, have := mem_loop_right h b tl φ h₁, exact this, exact hc} },
all_goals 
{rw h₂ at h₁, simp at h₁, apply mem_loop_right, exact h₁}
end

theorem mem_loop_box : Π h b m (rq : psig), rq ∈ dia_rule_loop h b m → rq.b = b 
| h b [] rq h₁ := absurd h₁ $ list.not_mem_nil _
| h b (hd :: tl) rq h₁ := 
begin
cases h₂ : hd,
case nnf.dia : ψ 
{rw h₂ at h₁, dsimp at h₁, 
 by_cases hc : ψ ∈ h, 
 {rw if_pos at h₁, cases h₁, rw h₁, apply mem_loop_box, exact h₁, exact hc},
 {rw if_neg at h₁, apply mem_loop_box, exact h₁, exact hc}},
all_goals 
{rw h₂ at h₁, simp at h₁, apply mem_loop_box, exact h₁}
end

theorem mem_loop_dia : Π h b m (rq : psig), rq ∈ dia_rule_loop h b m → ∃ (φ : nnf) (h : φ ∈ h), rq.d = φ
| h b [] rq h₁ := absurd h₁ $ list.not_mem_nil _
| h b (hd :: tl) rq h₁ := 
begin
cases h₂ : hd,
case nnf.dia : ψ 
{rw h₂ at h₁, dsimp at h₁, 
 by_cases hc : ψ ∈ h, 
 {rw if_pos at h₁, cases h₁, split, split, exact hc, rw h₁,
  apply mem_loop_dia, exact h₁, exact hc},
 {rw if_neg at h₁, apply mem_loop_dia, exact h₁, exact hc}},
all_goals 
{rw h₂ at h₁, simp at h₁, apply mem_loop_dia, exact h₁}
end

@[simp] def models_to_tmodels (l : list model) : list tmodel := 
list.map (λ x : model, x.1) l

theorem pt_of_m_to_tm (l : list model) : ∀ (m : tmodel), m ∈ models_to_tmodels l → (ptmodel m) ∧ global_pt m := 
list.mapp _ _ 
begin intros x hx, exact x.2 end

def box_new_rule_seqt {Γ Δ : sseqt} (i : box_new_instance_seqt Γ Δ) : node Δ → node Γ
| (closed h) := begin 
                  left, 
                  {apply unsat_of_closed_box_new, repeat {assumption}}, 
                end
| (open_ w)  := 
begin
right,
swap,
clear box_new_rule_seqt,
cases i with φ h₁ h₂,
cases w with w pw,
cases w with wt pwa,
cases wt with iw lw sgw,
let rhtk := box φ :: iw.htk,
have hhtk : hintikka rhtk,
  {split, 
   {intros n hn, cases hn, 
    {contradiction}, 
    {intro hne, cases hne, contradiction, 
     apply iw.hhtk.hno_contra, exact hn, exact hne} },
   {intros φ' ψ' h, cases h with heq hmem, 
    {injection heq with eq₁ eq₂},
    {right, 
     apply iw.hhtk.hand_left, exact hmem} },
   {intros φ' ψ' h, cases h with heq hmem, 
    {injection heq with eq₁ eq₂},
    {right,
     apply iw.hhtk.hand_right, exact hmem}},
   {intros φ' ψ' h, cases h with heq hmem,
    {contradiction},
    {have := iw.hhtk.hor hmem, cases this,
     {left, right, exact this}, 
     {right, right, exact this}}},
   {intros φ' h, cases h with heq hmem,
    {injection heq with heq', rw heq',
     right, apply iw.mhtk, simp at pw, rw pw, simp},
    {right, apply iw.hhtk.hbox, exact hmem}}},
have mhtk : Γ.m ⊆ rhtk,
  {intros x hx, by_cases heq : x = box φ, 
   {rw heq, simp}, 
   {have : x ∈ iw.Γ.m, 
     {simp at pw, rw pw, dsimp, right, 
      have := (mem_erase_of_ne heq).2 hx, exact this},
    right, apply iw.mhtk this }},
let im : info := ⟨Γ, rhtk, hhtk, mhtk⟩,  
let tm : tmodel := tmodel.cons im lw sgw,
have ptm : ptmodel tm, 
  {split,
   {simp, have := pwa.1.bhist, simp at pw, simp at this, rw pw at this, simp at this, 
    intros s hs φ hφ, apply this, exact hs, right, exact hφ},
   {simp, have := pwa.1.sbox, simp at this, 
    have hbhist := pwa.1.bhist, simp at hbhist,
    intros s hs ψ hψ, cases hψ,
    {apply hbhist _ hs, simp at pw, rw pw, simp, left, exact hψ},
    {apply this, exact hs, exact hψ}},
   {simp, have := pwa.1.pdia, simp at this, exact this},
   {simp, have := pwa.1.bdia, simp at pw, simp at this, 
    rw pw at this, simp at this, 
    intros s rq hdesc hmem, rw eq_desc_of_eq_children at hdesc, swap, exact iw, swap, exact sgw,
    have := this s rq hdesc hmem, 
    cases this with hl hr, 
    {left, exact hl}, 
    {right, rcases hr with ⟨d, hd⟩, rw eq_desc_of_eq_children at hd, split, exact hd} },
   {simp, have := pwa.1.reqb, simp at pw, simp at this, rw pw at this, simp at this, 
    intros rq hrq ψ hor, cases hor with hl hr, 
    {cases hl, apply this, exact hrq, right, left, exact hl, apply this, exact hrq, left, exact hl}, 
    {apply this, exact hrq, right, right, exact hr}},
   {simp, have := pwa.1.sreq, simp at pw, simp at this, rw pw at this, simp at this, exact this}},
have gpt : global_pt tm, 
  {intros s hs, have := pwa.2 s, rw eq_desc_of_eq_children at this, apply this, exact hs},
have hinfo : (minfo tm).Γ = Γ, {simp},
exact ⟨⟨tm, ⟨ptm, gpt⟩⟩, hinfo⟩
end

def box_rule_seqt {Γ Δ : sseqt} (i : box_dup_instance_seqt Γ Δ) : node Δ → node Γ
| (closed h) := begin 
                  left, 
                  {apply unsat_of_closed_box_dup, repeat {assumption}}, 
                end
| (open_ w)  := 
begin
right,
swap,
clear box_rule_seqt,
cases i with φ h₁ h₂,
cases w with w pw,
cases w with wt pwa,
cases wt with iw lw sgw,
let rhtk := box φ :: iw.htk,
have hhtk : hintikka rhtk,
  {split, 
   {intros n hn, cases hn, 
    {contradiction}, 
    {intro hne, cases hne, contradiction, 
     apply iw.hhtk.hno_contra, exact hn, exact hne} },
   {intros φ' ψ' h, cases h with heq hmem, 
    {injection heq with eq₁ eq₂},
    {right, 
     apply iw.hhtk.hand_left, exact hmem} },
   {intros φ' ψ' h, cases h with heq hmem, 
    {injection heq with eq₁ eq₂},
    {right,
     apply iw.hhtk.hand_right, exact hmem}},
   {intros φ' ψ' h, cases h with heq hmem,
    {contradiction},
    {have := iw.hhtk.hor hmem, cases this,
     {left, right, exact this}, 
     {right, right, exact this}}},
   {intros φ' h, cases h with heq hmem,
    {injection heq with heq', rw heq',
     right, apply iw.mhtk, simp at pw, rw pw, simp},
    {right, apply iw.hhtk.hbox, exact hmem}}},
have mhtk : Γ.m ⊆ rhtk,
  {intros x hx, by_cases heq : x = box φ, 
   {rw heq, simp}, 
   {have : x ∈ iw.Γ.m, 
     {simp at pw, rw pw, dsimp, right, 
      have := (mem_erase_of_ne heq).2 hx, exact this},
    right, apply iw.mhtk this }},
let im : info := ⟨Γ, rhtk, hhtk, mhtk⟩,  
let tm : tmodel := tmodel.cons im lw sgw,
have ptm : ptmodel tm, 
  {split,
   {simp, have := pwa.1.bhist, simp at pw, simp at this, rw pw at this, simp at this, 
    intros s hs φ hφ, apply this, exact hs, exact hφ},
   {simp, have := pwa.1.sbox, simp at this, 
    have hbhist := pwa.1.bhist, simp at hbhist,
    intros s hs ψ hψ, cases hψ,
    {apply hbhist _ hs, simp at pw, rw pw, simp, rw hψ, exact h₂},
    {apply this, exact hs, exact hψ}},
   {simp, have := pwa.1.pdia, simp at this, exact this},
   {simp, have := pwa.1.bdia, simp at pw, simp at this, 
    rw pw at this, simp at this, 
    intros s rq hdesc hmem, rw eq_desc_of_eq_children at hdesc, swap, exact iw, swap, exact sgw,
    have := this s rq hdesc hmem, 
    cases this with hl hr, 
    {left, exact hl}, 
    {right, rcases hr with ⟨d, hd⟩, rw eq_desc_of_eq_children at hd, split, exact hd} },
   {simp, have := pwa.1.reqb, simp at pw, simp at this, rw pw at this, simp at this, 
    intros rq hrq ψ hor, cases hor with hl hr, 
    {cases hl, apply this, exact hrq, right, rw hl, exact h₂, apply this, exact hrq, left, exact hl}, 
    {apply this, exact hrq, right, exact hr}},
   {simp, have := pwa.1.sreq, simp at pw, simp at this, rw pw at this, simp at this, exact this}},
have gpt : global_pt tm, 
  {intros s hs, have := pwa.2 s, rw eq_desc_of_eq_children at this, apply this, exact hs},
have hinfo : (minfo tm).Γ = Γ, {simp},
exact ⟨⟨tm, ⟨ptm, gpt⟩⟩, hinfo⟩
end

def build_model {Γ} (h : model_constructible Γ) : node Γ :=
begin
right,
split, swap,
{let mΓ : sseqt := Γ,
 let mhtk := Γ.m,
 have mhhtk : hintikka Γ.m, {apply hintikka_mc h},
 have mmhtk : Γ.m ⊆ Γ.m, {simp},
 split, swap,
 {let minfo : info := ⟨mΓ, mhtk, mhhtk, mmhtk⟩,
  exact tmodel.cons minfo [] [] },
 {split,
  {split,
   {simp},
   {simp},
   {simp, intros φ hφ, apply h.no_dia, exact hφ},
   {simp, intros s rq hdesc, exfalso, apply desc_not_nil, swap, exact hdesc, refl},
   {simp},
   {simp}},
  {intros x hx, exfalso, apply desc_not_nil, swap, exact hx, refl}}},
{simp}
end

def or_rule_seqt {Γ₁ Γ₂ Δ} (i : or_instance_seqt Δ Γ₁ Γ₂) : 
            node Γ₁ → node Γ₂ → node Δ
| (open_ w) _ := 
begin
right,
clear or_rule_seqt,
cases i with φ ψ h,
cases w with w pw,
cases w with wt pwa,
cases wt with iw lw sgw,
let rhtk := or φ ψ :: iw.htk,
have hhtk : hintikka rhtk,
  {split, 
   {intros n hn, cases hn, 
    {contradiction}, 
    {intro hne, cases hne, contradiction, 
     apply iw.hhtk.hno_contra, exact hn, exact hne} },
   {intros φ' ψ' h, cases h with heq hmem, 
    {injection heq with eq₁ eq₂},
    {right, 
     apply iw.hhtk.hand_left, exact hmem} },
   {intros φ' ψ' h, cases h with heq hmem, 
    {injection heq with eq₁ eq₂},
    {right,
     apply iw.hhtk.hand_right, exact hmem}},
   {intros φ' ψ' h, cases h with heq hmem,
    {injection heq with heq₁ heq₂, rw heq₁, rw heq₂, left, simp at pw, have := iw.mhtk, rw pw at this, simp at this, right, exact this.1},
    {have := iw.hhtk.hor hmem, cases this,
     {left, right, exact this}, 
     {right, right, exact this}}},
   {intros φ' h, cases h with heq hmem,
    {contradiction},
    {right, apply iw.hhtk.hbox, exact hmem}}},
have mhtk : Δ.m ⊆ rhtk,
  {intros x hx, by_cases heq : x = or φ ψ, 
   {rw heq, simp}, 
   {have : x ∈ iw.Γ.m, 
     {simp at pw, rw pw, dsimp, right, 
      have := (mem_erase_of_ne heq).2 hx, exact this},
    right, apply iw.mhtk this }},
let im : info := ⟨Δ, rhtk, hhtk, mhtk⟩,  
let tm : tmodel := tmodel.cons im lw sgw,
have ptm : ptmodel tm, 
  {split,
   {simp, have := pwa.1.bhist, simp at pw, simp at this, rw pw at this, simp at this, exact this},
   {simp, have := pwa.1.sbox, simp at this, exact this},
   {simp, have := pwa.1.pdia, simp at this, exact this},
   {simp, have := pwa.1.bdia, simp at pw, simp at this, 
    rw pw at this, simp at this, 
    intros s rq hdesc hmem, rw eq_desc_of_eq_children at hdesc, swap, exact iw, swap, exact sgw,
    have := this s rq hdesc hmem, 
    cases this with hl hr, 
    {left, exact hl}, 
    {right, rcases hr with ⟨d, hd⟩, rw eq_desc_of_eq_children at hd, split, exact hd} },
   {simp, have := pwa.1.reqb, simp at pw, simp at this, rw pw at this, simp at this, exact this},
   {simp, have := pwa.1.sreq, simp at pw, simp at this, rw pw at this, simp at this, exact this}},
have gpt : global_pt tm, 
  {intros s hs, have := pwa.2 s, rw eq_desc_of_eq_children at this, apply this, exact hs},
have hinfo : (minfo tm).Γ = Δ, {simp},
exact ⟨⟨tm, ⟨ptm, gpt⟩⟩, hinfo⟩
end
| _ (open_ w) := 
begin
right,
clear or_rule_seqt,
cases i with φ ψ h,
cases w with w pw,
cases w with wt pwa,
cases wt with iw lw sgw,
let rhtk := or φ ψ :: iw.htk,
have hhtk : hintikka rhtk,
  {split, 
   {intros n hn, cases hn, 
    {contradiction}, 
    {intro hne, cases hne, contradiction, 
     apply iw.hhtk.hno_contra, exact hn, exact hne} },
   {intros φ' ψ' h, cases h with heq hmem, 
    {injection heq with eq₁ eq₂},
    {right, 
     apply iw.hhtk.hand_left, exact hmem} },
   {intros φ' ψ' h, cases h with heq hmem, 
    {injection heq with eq₁ eq₂},
    {right,
     apply iw.hhtk.hand_right, exact hmem}},
   {intros φ' ψ' h, cases h with heq hmem,
    {injection heq with heq₁ heq₂, rw heq₁, rw heq₂, right, simp at pw, have := iw.mhtk, rw pw at this, simp at this, right, exact this.1},
    {have := iw.hhtk.hor hmem, cases this,
     {left, right, exact this}, 
     {right, right, exact this}}},
   {intros φ' h, cases h with heq hmem,
    {contradiction},
    {right, apply iw.hhtk.hbox, exact hmem}}},
have mhtk : Δ.m ⊆ rhtk,
  {intros x hx, by_cases heq : x = or φ ψ, 
   {rw heq, simp}, 
   {have : x ∈ iw.Γ.m, 
     {simp at pw, rw pw, dsimp, right, 
      have := (mem_erase_of_ne heq).2 hx, exact this},
    right, apply iw.mhtk this }},
let im : info := ⟨Δ, rhtk, hhtk, mhtk⟩,  
let tm : tmodel := tmodel.cons im lw sgw,
have ptm : ptmodel tm, 
  {split,
   {simp, have := pwa.1.bhist, simp at pw, simp at this, rw pw at this, simp at this, exact this},
   {simp, have := pwa.1.sbox, simp at this, exact this},
   {simp, have := pwa.1.pdia, simp at this, exact this},
   {simp, have := pwa.1.bdia, simp at pw, simp at this, 
    rw pw at this, simp at this, 
    intros s rq hdesc hmem, rw eq_desc_of_eq_children at hdesc, swap, exact iw, swap, exact sgw,
    have := this s rq hdesc hmem, 
    cases this with hl hr, 
    {left, exact hl}, 
    {right, rcases hr with ⟨d, hd⟩, rw eq_desc_of_eq_children at hd, split, exact hd} },
   {simp, have := pwa.1.reqb, simp at pw, simp at this, rw pw at this, simp at this, exact this},
   {simp, have := pwa.1.sreq, simp at pw, simp at this, rw pw at this, simp at this, exact this}},
have gpt : global_pt tm, 
  {intros s hs, have := pwa.2 s, rw eq_desc_of_eq_children at this, apply this, exact hs},
have hinfo : (minfo tm).Γ = Δ, {simp},
exact ⟨⟨tm, ⟨ptm, gpt⟩⟩, hinfo⟩
end
| (closed h₁) (closed h₂):= begin 
                              left,
                              apply unsat_of_closed_or_seqt, 
                              repeat {assumption}
                            end

