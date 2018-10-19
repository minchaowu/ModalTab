import .ops
open subtype nnf

class val_constructible (Γ : list nnf) extends saturated Γ:=
(no_contra : ∀ {n}, var n ∈ Γ → neg n ∉ Γ)
(v : list ℕ)
(hv : ∀ n, var n ∈ Γ ↔ n ∈ v)

class modal_applicable (Γ : list nnf) extends val_constructible Γ :=
(φ : nnf)
(ex : dia φ ∈ Γ)

class model_constructible (Γ : list nnf) extends val_constructible Γ :=
(no_dia : ∀ {φ}, nnf.dia φ ∉ Γ)

def unmodal (Γ : list nnf) : {x : list $ list nnf // 
(∀ i ∈ x, (node_size i < node_size Γ) ∧ 
(∀ φ, box φ ∈ Γ → φ ∈ i) ∧ 
(∀ {st : Type} (k : kripke st) s Δ 
(h₁ : ∀ φ, box φ ∈ Γ → box φ ∈ Δ) 
(h₂ : ∀ φ, dia φ ∈ Γ → dia φ ∈ Δ), 
sat k s Δ → ∃ s', sat k s' i) ∧ 
(dia (list.head i) ∈ Γ) ∧
Π h : unsatisfiable i, unsatisfiable (dia (list.head i) :: rebox (unbox Γ))) 
∧ 
∀ φ ∈ undia Γ, (φ :: unbox Γ) ∈ x} := 
list.smap _ (λ d, d :: (unbox Γ)) (undia Γ) 
(begin 
   intros φ hd, split, {apply undia_size hd}, 
   split,
   { intros ψ hb, right, apply (@unbox_iff Γ ψ).1, exact hb },
   split, 
   { intros st k s Δ h₁ h₂ h, 
     have : force k s (dia φ), 
       { apply h, apply h₂, rw undia_iff, exact hd }, 
     rcases this with ⟨w, hrel, hforce⟩,
     split, swap, {exact w}, 
     { intro ψ, intro hψ, cases hψ, 
       {rw hψ, exact hforce}, 
       {have := h₁ _ ((@unbox_iff Γ ψ).2 hψ), 
        have := h _ this,
        apply this _ hrel} } },
   split,
   { dsimp, rw undia_iff, exact hd },
   { intro h, intro, intros k s hsat, dsimp at hsat,
     have ex := hsat (dia φ) (by simp),
     cases ex with s' hs',
     apply h st k s', intros ψ hmem,
     cases hmem, 
     {rw hmem, exact hs'.2}, 
     {have := (@rebox_iff ψ (unbox Γ)).2 hmem, 
      apply hsat (box ψ) (by right; assumption) s' hs'.1 } }
end)

def unmodal_size (Γ : list nnf) : ∀ (i : list nnf),  i ∈ (unmodal Γ).1 → (node_size i < node_size Γ) := 
λ i hi, (((unmodal Γ).2.1) i hi).1

def unsat_of_unsat_unmodal {Γ : list nnf} (h : modal_applicable Γ) (i) : i ∈ (unmodal Γ).1 ∧ unsatisfiable i → unsatisfiable Γ := 
begin
  intro hex,
  intro, intros, intro h,
  have := ((unmodal Γ).2.1 i hex.1).2.2.1 k s Γ (λ x hx, hx) (λ x hx, hx) h, 
  cases this with w hw,
  exact hex.2 _ k w hw
end

/- Regular lemmas for the propositional part. -/

section
variables (φ ψ : nnf) (Γ₁ Γ₂ Δ : list nnf) {st : Type}
variables (k : kripke st) (s : st)
open list

theorem sat_subset (h₁ : Γ₁ ⊆ Γ₂) (h₂ : sat k s Γ₂) : sat k s Γ₁ :=
λ x hx, h₂ _ (h₁ hx)

theorem sat_sublist (h₁ : Γ₁ <+ Γ₂) (h₂ :sat k s Γ₂) : sat k s Γ₁ := 
sat_subset _ _ _ _ (subset_of_sublist h₁) h₂

theorem unsat_contra  {Δ n} : var n ∈ Δ →  neg n ∈ Δ →  unsatisfiable Δ:= 
begin
  intros h₁ h₂, intros v hsat, intros s hsat,
  have := hsat _ h₁, have := hsat _ h₂, simpa
end

theorem sat_of_and : force k s (and φ ψ) ↔ (force k s φ) ∧ (force k s ψ) := 
by split; {intro, simpa}; {intro, simpa}

theorem sat_of_sat_erase (h₁ : sat k s $ Δ.erase φ) (h₂ : force k s φ) : sat k s Δ := 
begin
  intro ψ, intro h,
  by_cases (ψ = φ),
  {rw h, assumption},
  {have : ψ ∈ Δ.erase φ,
   rw mem_erase_of_ne, assumption, exact h,
   apply h₁, assumption}
end

theorem unsat_and_of_unsat_split 
        (h₁ : and φ ψ ∈ Δ) 
        (h₂ : unsatisfiable $ φ :: ψ :: Δ.erase (and φ ψ)) : 
        unsatisfiable Δ :=
begin
  intro st, intros, intro h,
  apply h₂, swap 3, exact k, swap, exact s,
  intro e, intro he,
  cases he,
  {rw he, have := h _ h₁, rw sat_of_and at this, exact this.1},
  {cases he, 
    {rw he, have := h _ h₁, rw sat_of_and at this, exact this.2}, 
    {have := h _ h₁, apply h, apply mem_of_mem_erase he} }
end

theorem sat_and_of_sat_split
        (h₁ : and φ ψ ∈ Δ) 
        (h₂ : sat k s $ φ :: ψ :: Δ.erase (and φ ψ)) : 
        sat k s Δ := 
begin
  intro e, intro he,
  by_cases (e = and φ ψ),
  { rw h, dsimp, split, repeat {apply h₂, simp} },
  { have : e ∈ Δ.erase (and φ ψ),
      { rw mem_erase_of_ne, repeat { assumption } },
    apply h₂, simp [this] }
end

theorem unsat_or_of_unsat_split 
        (h : or φ ψ ∈ Δ) 
        (h₁ : unsatisfiable $ φ :: Δ.erase (nnf.or φ ψ)) 
        (h₂ : unsatisfiable $ ψ :: Δ.erase (nnf.or φ ψ)) : 
        unsatisfiable $ Δ := 
begin
  intro, intros, intro hsat,
  have := hsat _ h,
  dsimp at this,
  cases this,
  {apply h₁, swap 3, exact k, swap, exact s, intro e, intro he, 
   cases he, rw he, exact this, apply hsat, apply mem_of_mem_erase he},
  {apply h₂, swap 3, exact k, swap, exact s, intro e, intro he, 
   cases he, rw he, exact this, apply hsat, apply mem_of_mem_erase he}
end

theorem sat_or_of_sat_split_left 
        (h : or φ ψ ∈ Δ) 
        (hl : sat k s $ φ :: Δ.erase (nnf.or φ ψ)) :
        sat k s Δ := 
begin
  intros e he,
  by_cases (e = or φ ψ),
  { rw h, dsimp, left, apply hl, simp},
  {have : e ∈ Δ.erase (or φ ψ),
     { rw mem_erase_of_ne, repeat { assumption } },
   apply hl, simp [this]}
end

theorem sat_or_of_sat_split_right
        (h : or φ ψ ∈ Δ) 
        (hl : sat k s $ ψ :: Δ.erase (nnf.or φ ψ)) :
        sat k s Δ := 
begin
  intros e he,
  by_cases (e = or φ ψ),
  { rw h, dsimp, right, apply hl, simp},
  {have : e ∈ Δ.erase (or φ ψ),
     { rw mem_erase_of_ne, repeat { assumption } },
   apply hl, simp [this]}
end

end

/- Part of the soundness -/

theorem unsat_of_closed_and {Γ Δ} (i : and_instance Γ Δ) (h : unsatisfiable Δ) : unsatisfiable Γ := 
by cases i; { apply unsat_and_of_unsat_split, repeat {assumption} }

theorem unsat_of_closed_or {Γ₁ Γ₂ Δ : list nnf} (i : or_instance Δ Γ₁ Γ₂) (h₁ : unsatisfiable Γ₁) (h₂ : unsatisfiable Γ₂) : unsatisfiable Δ :=
by cases i; {apply unsat_or_of_unsat_split, repeat {assumption} }

/- Tree models -/

inductive model
| leaf : list nat → model
| cons : list nat → list model → model

instance : decidable_eq model := by tactic.mk_dec_eq_instance

open model

@[simp] def mval : nat → model → bool
| p (leaf v) := if p ∈ v then tt else ff
| p (cons v r) := if p ∈ v then tt else ff

@[simp] def mrel : model → model → bool
| (leaf v) m := ff
| (cons v r) m := if m ∈ r then tt else ff 

theorem mem_of_mrel_tt : Π {v r m}, mrel (cons v r) m = tt → m ∈ r :=
begin
  intros v r m h, by_contradiction,
  simpa using h
end

@[simp] def builder : kripke model := {val := mval, rel := mrel}

inductive batch_sat : list model → list (list nnf) → Prop
| bs_nil : batch_sat [] []
| bs_cons (m Γ l₁ l₂) : sat builder m Γ → batch_sat l₁ l₂ → 
                        batch_sat (m::l₁) (Γ::l₂) 

open batch_sat

theorem bs_ex : Π l Γ, 
batch_sat l Γ → ∀ m ∈ l, ∃ i ∈ Γ, sat builder m i
| l Γ bs_nil := λ m hm, by simpa using hm
| l Γ (bs_cons m Δ l₁ l₂ h hbs) := 
begin
  intros n hn, 
  cases hn,
  {split, swap, exact Δ, split, simp, rw hn, exact h},
  {have : ∃ (i : list nnf) (H : i ∈ l₂), sat builder n i,
     {apply bs_ex, exact hbs, exact hn},
  {rcases this with ⟨w, hw, hsat⟩, split, swap, exact w, split, 
   {simp [hw]}, {exact hsat} } }
end

theorem bs_forall : Π l Γ, 
batch_sat l Γ → ∀ i ∈ Γ, ∃ m ∈ l, sat builder m i
| l Γ bs_nil := λ m hm, by simpa using hm
| l Γ (bs_cons m Δ l₁ l₂ h hbs) := 
begin
  intros i hi,
  cases hi, {split, swap, exact m, split, simp, rw hi, exact h},
  {have : ∃ (n : model) (H : n ∈ l₁), sat builder n i,
     {apply bs_forall, exact hbs, exact hi},
  {rcases this with ⟨w, hw, hsat⟩, split, swap, exact w, split, 
   {simp [hw]}, {exact hsat} } }
end

theorem sat_of_batch_sat : Π l Γ (h : modal_applicable Γ), 
batch_sat l (unmodal Γ) → sat builder (cons h.v l) Γ := 
begin
  intros l Γ h hbs,
  intros φ hφ,
  cases hfml : φ,
  case nnf.var : n {dsimp, rw hfml at hφ, simp, apply if_pos, rw ←h.hv, exact hφ},
  case nnf.box : ψ 
  {dsimp, intros s' hs', have hmem := mem_of_mrel_tt hs', 
   have := bs_ex l (unmodal Γ) hbs s' hmem,
   rcases this with ⟨w, hw, hsat⟩,
   have := ((unmodal Γ).2.1 w hw).2.1 ψ _,
   swap, {rw ←hfml, exact hφ}, {apply hsat, exact this} },
  case nnf.dia : ψ 
  {dsimp, 
   have := bs_forall l (unmodal Γ) hbs (ψ :: unbox Γ) _, swap,
   {apply ((unmodal Γ).2.2), rw ←undia_iff, rw ←hfml, exact hφ}, 
   {rcases this with ⟨w, hw, hsat⟩, split, swap, exact w, split, 
    {simp [hw]}, {apply hsat, simp} } },
  case nnf.neg : n
  {dsimp, rw hfml at hφ, have : var n ∉ Γ, 
   {intro hin, have := h.no_contra, have := this hin, contradiction},
    simp, rw ←h.hv, exact this },
  case nnf.and : φ ψ
  {rw hfml at hφ, have := h.no_and, have := @this φ ψ, contradiction},
  case nnf.or : φ ψ
  {rw hfml at hφ, have := h.no_or, have := @this φ ψ, contradiction}
end

theorem build_model : Π Γ (h : model_constructible Γ), 
sat builder (leaf h.v) Γ := 
begin
  intros, intro, intro hmem,
  cases heq : φ,
  case nnf.var : n {dsimp, have := h.hv, rw heq at hmem, rw this at hmem, simp [hmem]},
  case nnf.neg : n {dsimp, have h₁ := h.hv, rw heq at hmem, have := h.no_contra, simp, rw ←h₁, intro hvar, apply this, swap, exact hmem, exact hvar},
  case nnf.box : φ {dsimp, intros, contradiction},
  case nnf.and : φ ψ { rw heq at hmem, have := h.no_and, have := @this φ ψ, contradiction},
  case nnf.or : φ ψ { rw heq at hmem, have := h.no_or, have := @this φ ψ, contradiction},
  case nnf.dia : φ { rw heq at hmem, have := h.no_dia, have := @this φ, contradiction},
end
