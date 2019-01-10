import .ops
open subtype nnf

def unmodal_seqt (Γ : seqt) : list seqt :=
list.map (λ d, {main := d :: (unbox (Γ.main ++ Γ.hdld)), hdld := []}) (undia (Γ.main ++ Γ.hdld))

def unmodal_seqt_size (Γ : seqt) : ∀ (i : seqt),  i ∈ unmodal_seqt Γ → (seqt_size i < seqt_size Γ) := 
list.mapp _ _ 
begin 
intros φ h, dsimp, constructor, simp [-list.map_append], 
apply undia_degree h
end


/- Regular lemmas for the propositional part. -/

section
variables (φ ψ : nnf) (Γ₁ Γ₂ Δ : list nnf) {st : Type}
variables (k : KT st) (s : st)
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

theorem unsat_contra_seqt {Δ : seqt} {n} : var n ∈ Δ.main →  neg n ∈ Δ.main →  unsatisfiable (Δ.main ++ Δ.hdld):= 
begin
  intros h₁ h₂, intros st m, intros s hsat,
  have := unsat_contra h₁ h₂,
  have := this _ m s,
  apply this,
  apply sat_subset _ _ _ _ _ hsat, 
  simp
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

theorem unsat_and_of_unsat_split_seqt {Γ}
        (h₁ : and φ ψ ∈ Δ) 
        (h₂ : unsatisfiable $ (φ :: ψ :: Δ.erase (and φ ψ)++Γ)) : 
        unsatisfiable (Δ++Γ) :=
begin
  intro st, intros, intro h,
  apply h₂, swap 3, exact k, swap, exact s,
  intro e, intro he,
  cases he,
  {rw he, have := h _ (mem_append_left _ h₁), rw sat_of_and at this, exact this.1},
  {cases he, 
    {rw he, have := h _ (mem_append_left _ h₁), rw sat_of_and at this, exact this.2},
    {have := h _ (mem_append_left _ h₁), apply h, apply mem_of_mem_erase, rw erase_append_left, exact he, exact h₁} }
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

theorem unsat_or_of_unsat_split_seqt {Γ}
        (h : or φ ψ ∈ Δ) 
        (h₁ : unsatisfiable $ (φ :: Δ.erase (nnf.or φ ψ)++Γ)) 
        (h₂ : unsatisfiable $ (ψ :: Δ.erase (nnf.or φ ψ)++Γ)) : 
        unsatisfiable $ (Δ++Γ) := 
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
  { have : e ∈ Δ.erase (or φ ψ),
      { rw mem_erase_of_ne, repeat { assumption } },
    apply hl, simp [this] }
end

end

/- Part of the soundness -/

theorem unsat_of_closed_and {Γ Δ} (i : and_instance Γ Δ) (h : unsatisfiable Δ) : unsatisfiable Γ := 
by cases i; { apply unsat_and_of_unsat_split, repeat {assumption} }

theorem unsat_of_closed_and_seqt {Γ Δ} (i : and_instance_seqt Γ Δ) (h : unsatisfiable (Δ.main++Δ.hdld)) : unsatisfiable (Γ.main++Γ.hdld) := 
begin
cases i,

end

#check unsat_and_of_unsat_split
-- by cases i; { apply unsat_and_of_unsat_split, repeat {assumption} }

-- theorem unsat_of_closed_or {Γ₁ Γ₂ Δ : list nnf} (i : or_instance Δ Γ₁ Γ₂) (h₁ : unsatisfiable Γ₁) (h₂ : unsatisfiable Γ₂) : unsatisfiable Δ :=
-- by cases i; {apply unsat_or_of_unsat_split, repeat {assumption} }

/- Tree models -/

inductive model
| cons : list ℕ → list model → model

instance : decidable_eq model := by tactic.mk_dec_eq_instance

open model

@[simp] def mval : ℕ → model → bool
| p (cons v r) := if p ∈ v then tt else ff

@[simp] def mrel : model → model → bool
| m₁@(cons v r) m₂ := if m₂ ∈ r ∨ m₁ = m₂ then tt else ff 

theorem refl_mrel (s : model) : mrel s s := by cases s with v r; simp

-- theorem mem_of_mrel_tt : Π {v r m}, mrel (cons v r) m = tt → m ∈ r :=
-- begin

-- end

@[simp] def builder : KT model := 
{val := λ n s, mval n s, rel := λ s₁ s₂, mrel s₁ s₂, refl := refl_mrel}

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

