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

@[simp] def force {states : Type} (k : S4 states) : states → nnf → Prop
| s (var n)    := k.val n s
| s (neg n)    := ¬ k.val n s
| s (and φ ψ)  := force s φ ∧ force s ψ
| s (or φ ψ)   := force s φ ∨ force s ψ
| s (box φ)    := ∀ s', k.rel s s' → force s' φ
| s (dia φ)    := ∃ s', k.rel s s' ∧ force s' φ

def sat {st} (k : S4 st) (s) (Γ : list nnf) : Prop := 
∀ φ ∈ Γ, force k s φ

def unsatisfiable (Γ : list nnf) : Prop := 
∀ (st) (k : S4 st) s, ¬ sat k s Γ

theorem unsat_singleton {φ} : unsatisfiable [φ] → ∀ (st) (k : S4 st) s, ¬ force k s φ
 := 
begin
  intro h, intros, intro hf, 
  apply h, intros ψ hψ, rw list.mem_singleton at hψ, rw hψ, exact hf
end

theorem sat_of_empty {st} (k : S4 st) (s) : sat k s [] :=
λ φ h, absurd h $ list.not_mem_nil _

theorem ne_empty_of_unsat {Γ} (h : unsatisfiable Γ): Γ ≠ [] := 
begin 
  intro heq, rw heq at h, 
  apply h, apply sat_of_empty, exact nat, 
  apply inhabited_S4.1, exact 0 
end

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

theorem mrel_nil (s v) (h : mrel (cons v []) s) : cons v [] = s :=
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

theorem mrel_of_mtrans {s₁ s₂} (h : mtrans s₁ s₂) : mrel s₁ s₂ :=
by by_cases heq : s₁ = s₂; {simp [heq, h]}

theorem mem_of_mtrans_tt : Π {v r m}, mtrans (cons v r) m = tt → (∃ s ∈ r, mtrans s m)
| v [] m h := by simp at h; contradiction
| v (hd::tl) m h := 
begin
  simp at h,
  cases h,
  {split, swap, exact hd, split, simp, exact h},
  {have := mem_of_mtrans_tt h, rcases this with ⟨w,hw,ht⟩, 
   split, swap, exact w, split, simp [hw], exact ht}
end

theorem mem_of_mrel_tt : Π {v r m}, mrel (cons v r) m = tt → (∃ s ∈ r, mrel s m) ∨ cons v r = m
| v [] m h := begin right, apply mrel_nil, exact h end
| v (hd::tl) m h := 
begin
  simp at h,
  rcases h with hl | hm | hr,
  {right, exact hl},
  {left, split, swap, exact hd, split, simp, apply mrel_of_mtrans hm},
  {have := mem_of_mtrans_tt hr, rcases this with ⟨w,hw,ht⟩, 
   left, split, swap, exact w, split, simp [hw], apply mrel_of_mtrans ht }
end

@[simp] def builder : S4 model := 
{val := λ n s, mval n s, rel := λ s₁ s₂, mrel s₁ s₂, refl := refl_mrel, trans := trans_mrel}

theorem force_box_of_leaf {v φ} (h : force builder (cons v []) φ): 
force builder (cons v []) (box φ) :=
begin
  dsimp, intros s' hs',
  have : cons v [] = s', {apply mrel_nil, exact hs'},
  rw ←this, assumption
end
