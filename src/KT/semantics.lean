import .ops
open subtype nnf model

def unmodal_seqt (Γ : seqt) : list seqt :=
list.map 
(λ d, 
{main := d :: (unbox (Γ.main ++ Γ.hdld)), hdld := [], 
 pmain := begin intros v hv φ hsat hin hall, exfalso, apply list.not_mem_nil, exact hin end, 
 phdld := box_only_nil}) 
(undia (Γ.main ++ Γ.hdld))

def unmodal_nil_hdld (Γ : seqt) : ∀ (i : seqt),  i ∈ unmodal_seqt Γ → (i.hdld = []) := 
list.mapp _ _ 
begin intros φ h, constructor end

def unmodal_seqt_size (Γ : seqt) : ∀ (i : seqt),  i ∈ unmodal_seqt Γ → (prod.measure_lex seqt_size i Γ) := 
list.mapp _ _ 
begin 
  intros φ h, 
  constructor, simp [-list.map_append], 
  apply undia_degree h
end

def unmodal_mem_box (Γ : seqt) : ∀ (i : seqt),  i ∈ unmodal_seqt Γ → (∀ φ, box φ ∈ Γ.main ++ Γ.hdld → φ ∈ i.main) := 
list.mapp _ _ begin intros φ h ψ hψ, right, apply (@unbox_iff (Γ.main++Γ.hdld) ψ).1 hψ end

def unmodal_sat_of_sat (Γ : seqt) : ∀ (i : seqt),  i ∈ unmodal_seqt Γ → 
(∀ {st : Type} (k : KT st) s Δ 
(h₁ : ∀ φ, box φ ∈ Γ.main++Γ.hdld → box φ ∈ Δ) 
(h₂ : ∀ φ, dia φ ∈ Γ.main++Γ.hdld → dia φ ∈ Δ), 
sat k s Δ → ∃ s', sat k s' i.main) :=
list.mapp _ _ 
begin
  intros φ hmem st k s Δ h₁ h₂ h, 
  have : force k s (dia φ), 
    { apply h, apply h₂, rw undia_iff, exact hmem }, 
  rcases this with ⟨w, hrel, hforce⟩,
  split, swap, {exact w}, 
  { intro ψ, intro hψ, cases hψ, 
    {rw hψ, exact hforce}, 
    {have := h₁ _ ((@unbox_iff (Γ.main++Γ.hdld) ψ).2 hψ), 
     have := h _ this,
     apply this _ hrel} },
end

-- TODO: Rewrite this ugly one.
def mem_unmodal_seqt (Γ : seqt) (φ) (h : φ ∈ undia (Γ.main++Γ.hdld)) : 
(⟨φ :: unbox (Γ.main++Γ.hdld), [], begin intros v hv φ hsat hin hall, exfalso, apply list.not_mem_nil, exact hin end, box_only_nil⟩ : seqt) ∈ unmodal_seqt Γ := 
begin 
  dsimp [unmodal_seqt], 
  apply list.mem_map_of_mem (λ φ, (⟨φ :: unbox (Γ.main++Γ.hdld), _,_,_⟩:seqt)) h 
end

def unsat_of_unsat_unmodal {Γ : seqt} (h : modal_applicable Γ) (i : seqt) : i ∈ unmodal_seqt Γ ∧ unsatisfiable (i.main ++ i.hdld) → unsatisfiable (Γ.main ++ Γ.hdld) := 
begin
  intro hex, intros st k s h,
  have := unmodal_sat_of_sat Γ i hex.1 k s (Γ.main ++ Γ.hdld) (λ x hx, hx) (λ x hx, hx) h,
  cases this with w hw,
  have := hex.2,
  rw (unmodal_nil_hdld _ _ hex.1) at this,
  simp at this,
  exact this _ _ _ hw
end

/- Part of the soundness -/

theorem unsat_of_closed_and {Γ Δ} (i : and_instance Γ Δ) (h : unsatisfiable Δ) : unsatisfiable Γ := 
by cases i; { apply unsat_and_of_unsat_split, repeat {assumption} }

theorem unsat_of_closed_and_seqt {Γ Δ} (i : and_instance_seqt Γ Δ) (h : unsatisfiable (Δ.main++Δ.hdld)) : unsatisfiable (Γ.main++Γ.hdld) := 
begin
cases i, {apply unsat_and_of_unsat_split_seqt, repeat {assumption} }
end

theorem unsat_of_closed_or_seqt {Γ₁ Γ₂ Δ : seqt} (i : or_instance_seqt Δ Γ₁ Γ₂) 
(h₁ : unsatisfiable (Γ₁.main++Γ₁.hdld)) 
(h₂ : unsatisfiable (Γ₂.main++Γ₂.hdld)) : 
unsatisfiable (Δ.main++Δ.hdld) :=
begin
cases i, {apply unsat_or_of_unsat_split_seqt, repeat {assumption}}
end

/- Tree models -/

inductive batch_sat_seqt : list model → list seqt → Prop
| bs_nil : batch_sat_seqt [] []
| bs_cons (m) (Γ:seqt) (l₁ l₂) : sat builder m (Γ.main++Γ.hdld) → 
                                 batch_sat_seqt l₁ l₂ → 
                                 batch_sat_seqt (m::l₁) (Γ::l₂)

open batch_sat_seqt

theorem bs_ex_seqt : Π l Γ, 
batch_sat_seqt l Γ → ∀ m ∈ l, ∃ i ∈ Γ, sat builder m (seqt.main i ++ i.hdld)
| l Γ bs_nil := λ m hm, by simpa using hm
| l Γ (bs_cons m Δ l₁ l₂ h hbs) := 
begin
  intros n hn, 
  cases hn,
  {split, swap, exact Δ, split, simp, rw hn, exact h},
  {have : ∃ (i : seqt) (H : i ∈ l₂), sat builder n (i.main ++ i.hdld),
     {apply bs_ex_seqt, exact hbs, exact hn},
  {rcases this with ⟨w, hw, hsat⟩, split, swap, exact w, split, 
   {simp [hw]}, {exact hsat} } }
end

theorem bs_forall_seqt : Π l Γ, 
batch_sat_seqt l Γ → ∀ i ∈ Γ, ∃ m ∈ l, sat builder m (seqt.main i ++ i.hdld)
| l Γ bs_nil := λ m hm, by simpa using hm
| l Γ (bs_cons m Δ l₁ l₂ h hbs) := 
begin
  intros i hi,
  cases hi, {split, swap, exact m, split, simp, rw hi, exact h},
  {have : ∃ (n : model) (H : n ∈ l₁), sat builder n (seqt.main i ++ i.hdld),
     {apply bs_forall_seqt, exact hbs, exact hi},
  {rcases this with ⟨w, hw, hsat⟩, split, swap, exact w, split, 
   {simp [hw]}, {exact hsat} } }
end

theorem sat_of_batch_sat_main : Π l Γ (h : modal_applicable Γ), 
batch_sat_seqt l (unmodal_seqt Γ) → 
sat builder (cons h.v l) (Γ.main) := 
begin
  intros l Γ h hbs,
  intros φ hφ,
  cases hfml : φ,
  case nnf.var : n 
  {rw hfml at hφ, simp, apply if_pos, rw ←h.hv, 
   exact hφ },
  case nnf.box : ψ 
  {exfalso, rw hfml at hφ, apply h.no_box_main, exact hφ},
  case nnf.dia : ψ 
  {dsimp, 
   let se : seqt := 
{main := ψ :: (unbox (Γ.main ++ Γ.hdld)), hdld := [], 
 pmain := begin intros v hv φ hsat hin hall, exfalso, apply list.not_mem_nil, exact hin end, 
 phdld := box_only_nil},
   have := bs_forall_seqt l (unmodal_seqt Γ) hbs se _, swap,
   {dsimp [unmodal_seqt], apply list.mem_map_of_mem (λ φ, (⟨φ :: unbox (Γ.main++Γ.hdld),_,_,_⟩:seqt)), rw ←undia_iff, rw ←hfml, simp [hφ] }, 
   {rcases this with ⟨w, hw, hsat⟩, split, swap, exact w, split, 
    {simp [hw]}, {apply hsat, simp} } },
  case nnf.neg : n
  {dsimp, rw hfml at hφ, have : var n ∉ Γ.main, 
   {intro hin, have := h.no_contra_main, have := this hin, contradiction},
    simp, rw ←h.hv, exact this },
  case nnf.and : φ ψ
  {rw hfml at hφ, have := h.satu.no_and, have := @this φ ψ, contradiction},
  case nnf.or : φ ψ
  {rw hfml at hφ, have := h.satu.no_or, have := @this φ ψ, contradiction}
end

theorem sat_of_batch_sat_box : Π l Γ (h : modal_applicable Γ), 
batch_sat_seqt l (unmodal_seqt Γ) → ∀ m∈l, ∀ φ, box φ ∈ Γ.hdld → force builder m φ := 
begin
  intros l Γ h hbs m hm φ hφ,
  have := bs_ex_seqt _ _ hbs _ hm,
  rcases this with ⟨i,hin,hi⟩,
  have := unmodal_mem_box _ _ hin φ,
  apply hi,
  rw list.mem_append, left,
  apply this, simp [hφ]
end

theorem sat_of_batch_sat : Π l Γ (h : modal_applicable Γ), 
batch_sat_seqt l (unmodal_seqt Γ) → 
sat builder (cons h.v l) (Γ.main++Γ.hdld) := 
begin
  intros l Γ h hbs,
  apply sat_append,
  {apply sat_of_batch_sat_main, assumption},
  {intros φ hφ, have := box_only_ex Γ.phdld hφ, 
   cases this with w hw,
   rw hw, dsimp, intros s' hs',
   have := mem_of_mrel_tt hs', cases this,
   {apply sat_of_batch_sat_box, exact h, exact hbs, exact this, rw hw at hφ, exact hφ},
   { rw ←this, apply Γ.pmain, 
     apply sat_of_batch_sat_main, exact hbs, rw hw at hφ, exact hφ, 
     { intros, apply sat_of_batch_sat_box, repeat {assumption} } }
}
end
