import defs
open nnf

structure seqt : Type :=
(main : list nnf)
(hdld : list nnf) -- handled boxes

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

inductive and_instance_seqt (Γ : seqt) : seqt → Type
| cons : Π {φ ψ}, nnf.and φ ψ ∈ Γ.main → 
         and_instance_seqt ⟨φ :: ψ :: Γ.main.erase (and φ ψ), Γ.hdld⟩
