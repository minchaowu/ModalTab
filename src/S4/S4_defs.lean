/-
Copyright (c) 2018-2019 Minchao Wu. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Minchao Wu
-/

import defs
open nnf tactic

meta def frame_restriction : tactic unit :=
do intro `a >> `[simp]

structure S4 (states : Type) extends kripke states :=
(refl  : reflexive rel . frame_restriction)
(trans : transitive rel . frame_restriction)

instance inhabited_S4 : inhabited (S4 ℕ) := 
⟨{ val := λ a b, tt, rel := λ a b, tt }⟩

inductive model
| cons : list ℕ → list model → model

instance : decidable_eq model := by tactic.mk_dec_eq_instance

open model

@[simp] def mval : ℕ → model → bool
| p (cons v r) := if p ∈ v then tt else ff

@[simp] def mtrans : model → model → bool
| (cons v []) m := ff
| (cons v (hd::tl)) m := if mtrans hd m then tt else mtrans (cons v tl) m

theorem trans_mtrans : Π s₁ s₂ s₃, mtrans s₁ s₂ → mtrans s₂ s₃ → mtrans s₁ s₃ 
| (cons v []) s₂ s₃ h₁ h₂ := begin exfalso, simp at h₁, exact h₁ end
| (cons v (hd::tl)) s₂ s₃ h₁ h₂ := 
begin
  by_cases h : mtrans hd s₂ = tt,
  { simp, apply if_pos, exact trans_mtrans _ _ _ h h₂ },
  { have : mtrans (cons v (hd :: tl)) s₃ = tt, 
    { simp, right, simp [h] at h₁, 
      have : ite ↥(mtrans hd s₂) tt (mtrans (cons v tl) s₂) = mtrans (cons v tl) s₂,
      { apply if_neg, exact h },
      rw this at h₁, exact trans_mtrans _ _ _ h₁ h₂ },
    exact this }
end

@[simp] def mrel : model → model → bool
| m₁ m₂ := if m₁ = m₂ then tt else mtrans m₁ m₂

theorem refl_mrel (s : model) : mrel s s := by cases s with v r; simp

theorem mrel_nil (s v) (h : mrel (cons v []) s) : s = cons v [] :=
begin
  by_cases hc : cons v [] = s,
  {rw hc},
  {have : mrel (cons v []) s = ff, {simp [hc]}, exfalso, 
   rw this at h, contradiction}
end

theorem trans_mrel (s₁ s₂ s₃) (h₁ : mrel s₁ s₂) (h₂ : mrel s₂ s₃) : mrel s₁ s₃ :=
begin
  by_cases heq₁ : s₁ = s₂,
  { rw ←heq₁ at h₂, exact h₂ },
  { by_cases heq₂ : s₂ = s₃, 
    { rw heq₂ at h₁, exact h₁ },
    { by_cases heq₃ : s₁ = s₃,
      { simp [heq₃] },
      { simp [heq₃], simp [heq₁] at h₁, simp [heq₂] at h₂, exact trans_mtrans _ _ _ h₁ h₂ } } }
end


