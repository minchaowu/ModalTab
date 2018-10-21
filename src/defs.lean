/-
Copyright (c) 2018 Minchao Wu. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Minchao Wu
-/
import data.list

open nat tactic subtype

inductive nnf : Type
| var (n : nat)         
| neg (n : nat)         
| and (φ ψ : nnf)       
| or (φ ψ : nnf)        
| box (φ : nnf)
| dia (φ : nnf)

open nnf
instance : inhabited nnf := ⟨nnf.var 0⟩

class no_literals (Γ : list nnf) :=
(no_var : ∀ {n}, var n ∉ Γ)
(no_neg : ∀ {n}, neg n ∉ Γ)

class saturated (Γ : list nnf) :=
(no_and : ∀ {φ ψ}, nnf.and φ ψ ∉ Γ)
(no_or : ∀ {φ ψ}, nnf.or φ ψ ∉ Γ)

class box_only (Γ : list nnf) extends no_literals Γ, saturated Γ :=
(no_dia : ∀ {φ}, nnf.dia φ ∉ Γ)

def nnf.to_string : nnf → string
| (var n)    := "P" ++ n.repr
| (neg n)    := "¬P" ++ n.repr
| (and φ ψ)  := nnf.to_string φ ++ "∧" ++ nnf.to_string ψ
| (or φ ψ)   := nnf.to_string φ ++ "∨" ++ nnf.to_string ψ
| (box φ)    := "□" ++ nnf.to_string φ 
| (dia φ)    := "⋄" ++ nnf.to_string φ

instance nnf_repr : has_repr nnf := ⟨nnf.to_string⟩

instance dec_eq_nnf : decidable_eq nnf := by mk_dec_eq_instance

structure kripke (states : Type) :=
(val       : nat → states → Prop)
(rel       : states → states → Prop)

instance inhabited_kripke : inhabited (kripke ℕ) := 
⟨{ val := λ a b, tt, rel := λ a b, tt }⟩

open nnf

/- This has a better computaional behaviour than a forcing relation defined explicitly as an inductive predicate. -/
@[simp] def force {states : Type} (k : kripke states) : states → nnf → Prop
| s (var n)    := k.val n s
| s (neg n)    := ¬ k.val n s
| s (and φ ψ)  := force s φ ∧ force s ψ
| s (or φ ψ)   := force s φ ∨ force s ψ
| s (box φ)    := ∀ s', k.rel s s' → force s' φ
| s (dia φ)    := ∃ s', k.rel s s' ∧ force s' φ

def sat {st} (k : kripke st) (s) (Γ : list nnf) : Prop := 
∀ φ ∈ Γ, force k s φ

def unsatisfiable (Γ : list nnf) : Prop := 
∀ (st) (k : kripke st) s, ¬ sat k s Γ

theorem unsat_singleton {φ} : unsatisfiable [φ] → ∀ (st) (k : kripke st) s, ¬ force k s φ
 := 
begin
  intro h, intros, intro hf, 
  apply h, intros ψ hψ, rw list.mem_singleton at hψ, rw hψ, exact hf
end

theorem sat_of_empty {st} (k : kripke st) (s) : sat k s [] :=
λ φ h, absurd h $ list.not_mem_nil _

theorem ne_empty_of_unsat {Γ} (h : unsatisfiable Γ): Γ ≠ [] := 
begin 
  intro heq, rw heq at h, 
  apply h, apply sat_of_empty, exact nat, 
  apply inhabited_kripke.1, exact 0 
end

/- Do not use map -/
@[simp] def node_size : list nnf → ℕ 
| []          := 0
| (hd :: tl)  := sizeof hd + node_size tl

inductive close_instance (Γ : list nnf)
| cons : Π {n}, var n ∈ Γ → neg n ∈ Γ → close_instance

inductive and_instance (Γ : list nnf) : list nnf → Type
| cons : Π {φ ψ}, nnf.and φ ψ ∈ Γ → 
         and_instance (φ :: ψ :: Γ.erase (nnf.and φ ψ))

inductive or_instance (Γ : list nnf) : list nnf → list nnf → Type
| cons : Π {φ ψ}, nnf.or φ ψ ∈ Γ → 
         or_instance (φ :: Γ.erase (nnf.or φ ψ)) 
                     (ψ :: Γ.erase (nnf.or φ ψ))

def left_prcp : Π {Γ₁ Γ₂ Δ : list nnf} (i : or_instance Δ Γ₁ Γ₂), nnf 
| Γ₁ Γ₂ Δ (@or_instance.cons _ φ ψ _) := φ
