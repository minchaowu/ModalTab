import .ops
open subtype nnf

structure KT (states : Type) extends kripke states :=
(refl  : reflexive rel)

instance inhabited_KT : inhabited (KT ℕ) := 
⟨{ val := λ a b, tt, rel := λ a b, tt, refl := λ a, by simp }⟩

@[simp] def force {states : Type} (k : KT states) : states → nnf → Prop
| s (var n)    := k.val n s
| s (neg n)    := ¬ k.val n s
| s (and φ ψ)  := force s φ ∧ force s ψ
| s (or φ ψ)   := force s φ ∨ force s ψ
| s (box φ)    := ∀ s', k.rel s s' → force s' φ
| s (dia φ)    := ∃ s', k.rel s s' ∧ force s' φ

def sat {st} (k : KT st) (s) (Γ : list nnf) : Prop := 
∀ φ ∈ Γ, force k s φ

def unsatisfiable (Γ : list nnf) : Prop := 
∀ (st) (k : KT st) s, ¬ sat k s Γ

theorem unsat_singleton {φ} : unsatisfiable [φ] → ∀ (st) (k : KT st) s, ¬ force k s φ
 := 
begin
  intro h, intros, intro hf, 
  apply h, intros ψ hψ, rw list.mem_singleton at hψ, rw hψ, exact hf
end

theorem sat_of_empty {st} (k : KT st) (s) : sat k s [] :=
λ φ h, absurd h $ list.not_mem_nil _

theorem ne_empty_of_unsat {Γ} (h : unsatisfiable Γ): Γ ≠ [] := 
begin 
  intro heq, rw heq at h, 
  apply h, apply sat_of_empty, exact nat, 
  apply inhabited_KT.1, exact 0 
end

class val_constructible (Γ : seqt) :=
(satu : saturated Γ.main)
(no_box_main : ∀ {φ}, box φ ∉ Γ.main)
(no_contra_main : ∀ {n}, var n ∈ Γ.main → neg n ∉ Γ.main)
(v : list ℕ)
(hv : ∀ n, var n ∈ Γ.main ↔ n ∈ v)

class modal_applicable (Γ : seqt) extends val_constructible Γ :=
(φ : nnf)
(ex : dia φ ∈ Γ.main)

class model_constructible (Γ : seqt) extends val_constructible Γ :=
(no_dia : ∀ {φ}, nnf.dia φ ∉ Γ.main)

def unmodal_seqt (Γ : seqt) : list seqt :=
list.map (λ d, {main := d :: (unbox (Γ.main ++ Γ.hdld)), hdld := []}) (undia (Γ.main ++ Γ.hdld))

def unmodal_seqt_size (Γ : seqt) : ∀ (i : seqt),  i ∈ unmodal_seqt Γ → (seqt_size i < seqt_size Γ) := 
list.mapp _ _ 
begin 
intros φ h, dsimp, constructor, simp [-list.map_append], 
end

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
