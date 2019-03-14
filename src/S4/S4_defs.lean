/-
Copyright (c) 2018-2019 Minchao Wu. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Minchao Wu
-/

import defs data.list.perm
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


structure psig : Type :=
(d : nnf)
(b : list nnf)

def sig : Type := option psig

inductive model
| cons (h : list nnf) (a b : list psig) (s : sig): list model → model


open nnf

@[simp] def sub_nnf : nnf → list nnf
| (var n)    := [var n]
| (neg n)    := [neg n]
| (and φ ψ)  := and φ ψ :: (sub_nnf φ ++ sub_nnf ψ)
| (or φ ψ)   := or φ ψ :: (sub_nnf φ ++ sub_nnf ψ)
| (box φ)    := box φ :: sub_nnf φ
| (dia φ)    := dia φ :: sub_nnf φ

theorem mem_sub_nnf_self : Π φ : nnf, φ ∈ sub_nnf φ :=
begin intro φ, cases φ,  all_goals {simp} end 

theorem mem_sub_nnf_and {φ ψ : nnf} : Π γ : nnf, and φ ψ ∈ sub_nnf γ → φ ∈ sub_nnf γ ∧ ψ ∈ sub_nnf γ
| (var n) h   := begin simp at h, contradiction end
| (neg n) h   := begin simp at h, contradiction end 
| (and φ₁ ψ₁) h := 
begin 
simp only [sub_nnf] at h, 
cases h, 
{injection h with eq₁ eq₂, 
 rw eq₁, rw eq₂, 
 simp only [sub_nnf], 
 split, 
 {simp, right, left, apply mem_sub_nnf_self}, 
 {simp, right, right, apply mem_sub_nnf_self}},
{have := (@list.mem_append _ _ _ _).1 h,  
 cases this,
 {split,
  {simp, right, left, apply (mem_sub_nnf_and _ _).1, exact this},
  {simp, right, left, apply (mem_sub_nnf_and _ _).2, exact this}},
 {split, 
  {simp, right, right, apply (mem_sub_nnf_and _ _).1, exact this},
  {simp, right, right, apply (mem_sub_nnf_and _ _).2, exact this}}}
end
| (or φ₁ ψ₁) h  := 
begin 
simp at h,
cases h,
 {split,
  {simp, right, left, apply (mem_sub_nnf_and _ _).1, exact h},
  {simp, right, left, apply (mem_sub_nnf_and _ _).2, exact h}},
 {split, 
  {simp, right, right, apply (mem_sub_nnf_and _ _).1, exact h},
  {simp, right, right, apply (mem_sub_nnf_and _ _).2, exact h}}
end
| (box φ₁) h   := 
begin
simp at h,
{split,
 {simp, right, apply (mem_sub_nnf_and _ _).1, exact h},
 {simp, right, apply (mem_sub_nnf_and _ _).2, exact h}}
end
| (dia φ₁) h   := 
begin
simp at h,
{split,
 {simp, right, apply (mem_sub_nnf_and _ _).1, exact h},
 {simp, right, apply (mem_sub_nnf_and _ _).2, exact h}}
end

theorem mem_sub_nnf_or {φ ψ : nnf} : Π γ : nnf, or φ ψ ∈ sub_nnf γ → φ ∈ sub_nnf γ ∧ ψ ∈ sub_nnf γ
| (var n) h   := begin simp at h, contradiction end
| (neg n) h   := begin simp at h, contradiction end 
| (and φ₁ ψ₁) h := 
begin 
simp at h,
cases h,
 {split,
  {simp, right, left, apply (mem_sub_nnf_or _ _).1, exact h},
  {simp, right, left, apply (mem_sub_nnf_or _ _).2, exact h}},
 {split, 
  {simp, right, right, apply (mem_sub_nnf_or _ _).1, exact h},
  {simp, right, right, apply (mem_sub_nnf_or _ _).2, exact h}}
end
| (or φ₁ ψ₁) h  := 
begin 
simp only [sub_nnf] at h, 
cases h, 
{injection h with eq₁ eq₂, 
 rw eq₁, rw eq₂, 
 simp only [sub_nnf], 
 split, 
 {simp, right, left, apply mem_sub_nnf_self}, 
 {simp, right, right, apply mem_sub_nnf_self}},
{have := (@list.mem_append _ _ _ _).1 h,  
 cases this,
 {split,
  {simp, right, left, apply (mem_sub_nnf_or _ _).1, exact this},
  {simp, right, left, apply (mem_sub_nnf_or _ _).2, exact this}},
 {split, 
  {simp, right, right, apply (mem_sub_nnf_or _ _).1, exact this},
  {simp, right, right, apply (mem_sub_nnf_or _ _).2, exact this}}}
end
| (box φ₁) h   := 
begin
simp at h,
{split,
 {simp, right, apply (mem_sub_nnf_or _ _).1, exact h},
 {simp, right, apply (mem_sub_nnf_or _ _).2, exact h}}
end
| (dia φ₁) h   := 
begin
simp at h,
{split,
 {simp, right, apply (mem_sub_nnf_or _ _).1, exact h},
 {simp, right, apply (mem_sub_nnf_or _ _).2, exact h}}
end

theorem mem_sub_nnf_box {φ : nnf} : Π γ : nnf, box φ ∈ sub_nnf γ → φ ∈ sub_nnf γ
| (var n) h   := begin simp at h, contradiction end
| (neg n) h   := begin simp at h, contradiction end 
| (and φ₁ ψ₁) h := 
begin 
simp at h, 
cases h, 
{simp, right, left, apply mem_sub_nnf_box, exact h},
{simp, right, right, apply mem_sub_nnf_box, exact h}
end
| (or φ₁ ψ₁) h  := 
begin 
simp at h,
cases h, 
{simp, right, left, apply mem_sub_nnf_box, exact h},
{simp, right, right, apply mem_sub_nnf_box, exact h}
end
| (box φ₁) h   := 
begin
simp at h,
cases h, 
{rw h, simp, right, apply mem_sub_nnf_self},
{simp, right, apply mem_sub_nnf_box, exact h}
end
| (dia φ₁) h   := 
begin
simp at h,
simp, right, apply mem_sub_nnf_box, exact h
end

theorem mem_sub_nnf_dia {φ : nnf} : Π γ : nnf, dia φ ∈ sub_nnf γ → φ ∈ sub_nnf γ
| (var n) h   := begin simp at h, contradiction end
| (neg n) h   := begin simp at h, contradiction end 
| (and φ₁ ψ₁) h := 
begin 
simp at h, 
cases h, 
{simp, right, left, apply mem_sub_nnf_dia, exact h},
{simp, right, right, apply mem_sub_nnf_dia, exact h}
end
| (or φ₁ ψ₁) h  := 
begin 
simp at h,
cases h, 
{simp, right, left, apply mem_sub_nnf_dia, exact h},
{simp, right, right, apply mem_sub_nnf_dia, exact h}
end
| (box φ₁) h   := 
begin
simp at h,
simp, right, apply mem_sub_nnf_dia, exact h
end
| (dia φ₁) h   := 
begin
simp at h,
cases h, 
{rw h, simp, right, apply mem_sub_nnf_self},
{simp, right, apply mem_sub_nnf_dia, exact h}
end

@[simp] def closure : list nnf → list nnf
| [] := []
| (hd::tl) := sub_nnf hd ++ closure tl

theorem mem_closure_and {φ ψ : nnf} : Π Γ : list nnf, and φ ψ ∈ closure Γ → φ ∈ closure Γ ∧ ψ ∈ closure Γ
| [] h := absurd h $ list.not_mem_nil _
| (hd::tl) h := 
begin
simp at h,
cases h,
{split,
 {simp, left, apply (mem_sub_nnf_and hd _).1, swap, exact h},
 {simp, left, apply (mem_sub_nnf_and hd _).2, swap, exact h}},
{split,
 {simp, right, apply (mem_closure_and _ _).1, exact h},
 {simp, right, apply (mem_closure_and _ _).2, exact h} }
end

theorem mem_closure_box {φ : nnf} : Π Γ : list nnf, box φ ∈ closure Γ → φ ∈ closure Γ
| [] h := absurd h $ list.not_mem_nil _
| (hd::tl) h := 
begin
simp at h,
cases h,
{simp, left, apply mem_sub_nnf_box _ h},
{simp, right, apply mem_closure_box _ h}
end

theorem mem_closure_dia {φ : nnf} : Π Γ : list nnf, dia φ ∈ closure Γ → φ ∈ closure Γ
| [] h := absurd h $ list.not_mem_nil _
| (hd::tl) h := 
begin
simp at h,
cases h,
{simp, left, apply mem_sub_nnf_dia _ h},
{simp, right, apply mem_closure_dia _ h}
end


namespace list
universes u v w
variables {α : Type u}

theorem length_sub_lt_of_nodup_subperm [decidable_eq α] {l₁ l₂ : list α} {a : α} 
(h₁ : l₁ <+~ l₂) (h₂ : a ∈ l₂) (h₃ : a ∉ l₁) (h₄ : nodup l₁):
length l₂ - length (a :: l₁) < length l₂ - length l₁
:=
begin
rw nat.sub_lt_sub_left_iff,
{simp, apply zero_lt_one}, 
{apply length_le_of_subperm, apply cons_subperm_of_mem, repeat {assumption}}
end

theorem nil_subperm {l : list α} : [] <+~ l := 
⟨[], perm.nil, by simp⟩ 

end list

structure sseqt : Type :=
(goal : list nnf)
(s : sig)
(a : list psig)
(h b m: list nnf)
(ndh : list.nodup h)
(ndb : list.nodup b)
(sph : h <+~ closure goal)
(spb : b <+~ closure goal)
(sbm : m ⊆ closure goal)

def sseqt_size (s : sseqt) : ℕ × ℕ × ℕ := 
((closure s.goal).length - s.b.length, 
 (closure s.goal).length - s.h.length, 
 node_size s.m)

def and_child {φ ψ} (Γ : sseqt) (h : nnf.and φ ψ ∈ Γ.m) : sseqt :=
{ goal := Γ.goal, 
  s := none,
  a := Γ.a, 
  h := Γ.h, 
  b := Γ.b, 
  m := φ :: ψ :: Γ.m.erase (and φ ψ),
  ndh := Γ.ndh,
  ndb := Γ.ndb,
  sph := Γ.sph,
  spb := Γ.spb,
  sbm := begin 
          intros x hx, cases hx, 
          {rw hx, apply (mem_closure_and _ (Γ.sbm h)).1}, 
          {cases hx, 
           {rw hx, apply (mem_closure_and _ (Γ.sbm h)).2},
           {apply Γ.sbm, apply list.erase_subset, exact hx}}
         end }

inductive and_instance_seqt (Γ : sseqt) : sseqt → Type
| cons : Π {φ ψ} (h : nnf.and φ ψ ∈ Γ.m), 
         and_instance_seqt $ and_child Γ h

def box_child_new {φ} (Γ : sseqt) (h₁ : nnf.box φ ∈ Γ.m) (h₂ : nnf.box φ ∉ Γ.b) : sseqt :=
{ goal := Γ.goal, 
  s := none,
  a := Γ.a, 
  h := [], 
  b := box φ :: Γ.b, 
  m := φ :: Γ.m.erase (box φ),
  ndh := by simp,
  ndb := begin rw list.nodup_cons, split, exact h₂, exact Γ.ndb end,
  sph := begin apply list.nil_subperm end,
  spb := begin 
           apply list.cons_subperm_of_mem Γ.ndb h₂, 
           apply Γ.sbm h₁, apply Γ.spb
         end,
  sbm := begin 
           intros x hx, cases hx, 
           {rw hx, apply mem_closure_box _ (Γ.sbm h₁)}, 
           {apply Γ.sbm, apply list.erase_subset, exact hx}
         end }

def box_child {φ} (Γ : sseqt) (h₁ : nnf.box φ ∈ Γ.m) : sseqt :=
{ goal := Γ.goal, 
  s := none,
  a := Γ.a, 
  h := Γ.h, 
  b := Γ.b, 
  m := φ :: Γ.m.erase (box φ),
  ndh := Γ.ndh,
  ndb := Γ.ndb,
  sph := Γ.sph,
  spb := Γ.spb,
  sbm := begin 
           intros x hx, cases hx, 
           {rw hx, apply mem_closure_box _ (Γ.sbm h₁)}, 
           {apply Γ.sbm, apply list.erase_subset, exact hx}
         end }


@[simp] def filter_dia (l : list nnf) : list nnf → list nnf
| [] := []
| (var n::tl) := var n :: filter_dia tl
| (neg n::tl) := neg n :: filter_dia tl
| (and φ ψ::tl) := and φ ψ :: filter_dia tl
| (or φ ψ::tl) := or φ ψ :: filter_dia tl
| (box φ::tl) := box φ :: filter_dia tl
| (dia φ::tl) := if φ ∈ l then filter_dia tl else φ :: filter_dia tl

@[simp] def filter_undia (l : list nnf) : list nnf → list nnf
| [] := []
| (dia φ::tl) := if φ ∈ l then filter_undia tl else φ :: filter_undia tl
| (e::tl) := filter_undia tl

theorem mem_filter_undia_left : Π l Γ φ (h₁ : dia φ ∈ Γ) (h₂ : φ ∉ l),
φ ∈ filter_undia l Γ
| l [] φ h₁ h₂ := absurd h₁ $ list.not_mem_nil _
| l (hd :: tl) φ h₁ h₂ := 
begin
cases h : hd,
case nnf.dia : ψ 
{rw h at h₁, simp, 
 by_cases hc : ψ ∈ l,
 {rw if_pos, apply mem_filter_undia_left, cases h₁, {injection h₁ with h₁', rw ←h₁' at hc, contradiction}, {exact h₁}, repeat {assumption}},
 {rw if_neg, cases h₁, {injection h₁ with h₁', rw h₁', simp}, {right, apply mem_filter_undia_left, exact h₁, exact h₂}, exact hc}},
all_goals 
{simp, rw h at h₁, cases h₁, contradiction, apply mem_filter_undia_left, repeat {assumption}}
end

theorem mem_filter_dia_right_aux : Π l Γ φ, φ ∈ filter_undia l Γ → dia φ ∈ Γ 
| l [] φ h := absurd h $ list.not_mem_nil _
| l (hd :: tl) φ h := 
begin
cases h₁ : hd,
case nnf.dia : ψ 
{rw h₁ at h, dsimp at h, 
 by_cases hc : ψ ∈ l, 
 {rw if_pos at h, have := mem_filter_dia_right_aux l tl φ h, right, exact this, exact hc},
 {rw if_neg at h, cases h, {rw h, simp}, {have := mem_filter_dia_right_aux l tl φ h, right, exact this}, exact hc}},
all_goals 
{rw h₁ at h, simp at h, right, apply mem_filter_dia_right_aux, exact h}
end

theorem mem_filter_dia_right : Π l Γ φ (h₂ : φ ∈ filter_undia l Γ), φ ∉ l
| l [] φ h := absurd h $ list.not_mem_nil _
| l (hd :: tl) φ h := 
begin 
cases h₁ : hd,
case nnf.dia : ψ 
{rw h₁ at h, dsimp at h, 
 by_cases hc : ψ ∈ l, 
 {rw if_pos at h, have := mem_filter_dia_right l tl φ h, exact this, exact hc},
 {rw if_neg at h, cases h, {rw h, exact hc}, {have := mem_filter_dia_right l tl φ h, exact this}, exact hc}},
all_goals 
{rw h₁ at h, simp at h, apply mem_filter_dia_right, exact h}
end
