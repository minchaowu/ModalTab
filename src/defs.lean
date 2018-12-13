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
| (box φ)    := "□" ++ "(" ++ nnf.to_string φ ++ ")"
| (dia φ)    := "◇" ++ "(" ++ nnf.to_string φ ++ ")"

instance nnf_repr : has_repr nnf := ⟨nnf.to_string⟩

instance dec_eq_nnf : decidable_eq nnf := by mk_dec_eq_instance

structure kripke (states : Type) :=
(val       : ℕ → states → Prop)
(rel       : states → states → Prop)

instance inhabited_kripke : inhabited (kripke ℕ) := 
⟨{ val := λ a b, tt, rel := λ a b, tt }⟩

open nnf

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
