import defs
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

/- Tree models -/

inductive model
| cons : list ℕ → list model → model

instance : decidable_eq model := by tactic.mk_dec_eq_instance

open model

@[simp] def mval : ℕ → model → bool
| p (cons v r) := if p ∈ v then tt else ff

@[simp] def mrel : model → model → bool
| m₁@(cons v r) m₂ := if m₂ ∈ r ∨ m₁ = m₂ then tt else ff 

