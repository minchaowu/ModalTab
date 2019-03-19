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

instance : decidable_eq psig := by tactic.mk_dec_eq_instance

def sig : Type := option psig

instance : decidable_eq sig := by tactic.mk_dec_eq_instance

def dsig : Π (s : sig) (h : s ≠ none), nnf
| none h := by contradiction
| (some ⟨d, b⟩) h := d

def bsig : Π (s : sig) (h : s ≠ none), list nnf
| none h := by contradiction
| (some ⟨d, b⟩) h := b

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

theorem mem_closure_self : Π Γ : list nnf, Γ ⊆ closure Γ
| [] := λ x h, absurd h $ list.not_mem_nil _
| (hd::tl) := 
begin 
intros x hx, cases hx, 
{rw hx, simp, left, apply mem_sub_nnf_self},
{simp, right, apply mem_closure_self, exact hx} 
end

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

theorem mem_closure_or {φ ψ : nnf} : Π Γ : list nnf, or φ ψ ∈ closure Γ → φ ∈ closure Γ ∧ ψ ∈ closure Γ
| [] h := absurd h $ list.not_mem_nil _
| (hd::tl) h := 
begin
simp at h,
cases h,
{split,
 {simp, left, apply (mem_sub_nnf_or hd _).1, swap, exact h},
 {simp, left, apply (mem_sub_nnf_or hd _).2, swap, exact h}},
{split,
 {simp, right, apply (mem_closure_or _ _).1, exact h},
 {simp, right, apply (mem_closure_or _ _).2, exact h} }
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

instance (Γ) : decidable_eq (no_literals Γ) := by tactic.mk_dec_eq_instance

instance (Γ) : decidable_eq (saturated Γ) := by tactic.mk_dec_eq_instance

instance (Γ) : decidable_eq (box_only Γ) := by tactic.mk_dec_eq_instance

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
(ha : ∀ φ ∈ h, (⟨φ, b⟩ : psig) ∈ a)
(hb : box_only b)
(ps₁ : Π (h : s ≠ none), dsig s h ∈ m)
(ps₂ : Π (h : s ≠ none), bsig s h ⊆ m)

instance : decidable_eq sseqt := by tactic.mk_dec_eq_instance

class val_constructible (Γ : sseqt) :=
(satu : saturated Γ.m)
(no_box_main : ∀ {φ}, box φ ∉ Γ.m)
(no_contra_main : ∀ {n}, var n ∈ Γ.m → neg n ∉ Γ.m)

class modal_applicable (Γ : sseqt) extends val_constructible Γ :=
(φ : nnf)
(ex : dia φ ∈ Γ.m)

class model_constructible (Γ : sseqt) extends val_constructible Γ :=
(no_dia : ∀ {φ}, nnf.dia φ ∉ Γ.m)

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
         end,
  ha := Γ.ha,
  hb := Γ.hb,
  ps₁ := by intro; contradiction,
  ps₂ := by intro; contradiction}

inductive and_instance_seqt (Γ : sseqt) : sseqt → Type
| cons : Π {φ ψ} (h : nnf.and φ ψ ∈ Γ.m), 
         and_instance_seqt $ and_child Γ h

def or_child_left {φ ψ} (Γ : sseqt) (h : nnf.or φ ψ ∈ Γ.m) : sseqt :=
{ goal := Γ.goal, 
  s := none,
  a := Γ.a, 
  h := Γ.h, 
  b := Γ.b, 
  m := φ :: Γ.m.erase (or φ ψ),
  ndh := Γ.ndh,
  ndb := Γ.ndb,
  sph := Γ.sph,
  spb := Γ.spb,
  sbm := begin 
          intros x hx, cases hx, 
          {rw hx, apply (mem_closure_or _ (Γ.sbm h)).1}, 
          {apply Γ.sbm, apply list.erase_subset, exact hx}
         end,
  ha := Γ.ha,
  hb := Γ.hb,
  ps₁ := by intro; contradiction,
  ps₂ := by intro; contradiction}

def or_child_right {φ ψ} (Γ : sseqt) (h : nnf.or φ ψ ∈ Γ.m) : sseqt :=
{ goal := Γ.goal, 
  s := none,
  a := Γ.a, 
  h := Γ.h, 
  b := Γ.b, 
  m := ψ :: Γ.m.erase (or φ ψ),
  ndh := Γ.ndh,
  ndb := Γ.ndb,
  sph := Γ.sph,
  spb := Γ.spb,
  sbm := begin 
          intros x hx, cases hx, 
          {rw hx, apply (mem_closure_or _ (Γ.sbm h)).2}, 
          {apply Γ.sbm, apply list.erase_subset, exact hx}
         end,
  ha := Γ.ha,
  hb := Γ.hb,
  ps₁ := by intro; contradiction,
  ps₂ := by intro; contradiction}

inductive or_instance_seqt (Γ : sseqt) : sseqt → sseqt → Type
| cons : Π {φ ψ} (h : nnf.or φ ψ ∈ Γ.m),
         or_instance_seqt (or_child_left Γ h) (or_child_right Γ h)

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
         end,
  ha := λ φ h, absurd h $ list.not_mem_nil _,
  hb := cons_box_only Γ.hb,
  ps₁ := by intro; contradiction,
  ps₂ := by intro; contradiction}

inductive box_new_instance_seqt (Γ : sseqt) : sseqt → Type
| cons : Π {φ} (h₁ : nnf.box φ ∈ Γ.m) (h₂ : nnf.box φ ∉ Γ.b), 
         box_new_instance_seqt $ box_child_new Γ h₁ h₂

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
         end,
  ha := Γ.ha,
  hb := Γ.hb,
  ps₁ := by intro; contradiction,
  ps₂ := by intro; contradiction}

inductive box_dup_instance_seqt (Γ : sseqt) : sseqt → Type
| cons : Π {φ} (h₁ : nnf.box φ ∈ Γ.m) (h₂ : nnf.box φ ∈ Γ.b), 
         box_dup_instance_seqt $ box_child Γ h₁

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

structure hintikka (Γ : list nnf) : Prop :=
(hno_contra : ∀ {n}, var n ∈ Γ → neg n ∉ Γ)
(hand_left : ∀ {φ ψ}, nnf.and φ ψ ∈ Γ → φ ∈ Γ)
(hand_right : ∀ {φ ψ}, nnf.and φ ψ ∈ Γ → ψ ∈ Γ)
(hor : ∀ {φ ψ}, nnf.or φ ψ ∈ Γ → φ ∈ Γ ∨ ψ ∈ Γ)
(hbox : ∀ {φ}, nnf.box φ ∈ Γ → φ ∈ Γ)

theorem hintikka_vc {Γ} (h : val_constructible Γ) : hintikka Γ.m :=
{hno_contra := h.no_contra_main,
 hand_left := begin intros φ ψ h₁, exfalso, apply h.satu.no_and, exact h₁ end,
 hand_right := begin intros φ ψ h₁, exfalso, apply h.satu.no_and, exact h₁ end,
 hor := begin intros φ ψ h₁, exfalso, apply h.satu.no_or, exact h₁ end,
 hbox := begin intros φ h₁, exfalso, apply h.no_box_main, exact h₁ end}

theorem hintikka_ma {Γ} (h : modal_applicable Γ) : hintikka Γ.m :=
hintikka_vc h.to_val_constructible

theorem hintikka_mc {Γ} (h : model_constructible Γ) : hintikka Γ.m :=
hintikka_vc h.to_val_constructible

structure info : Type :=
(Γ : sseqt)
(htk : list nnf)
(hhtk : hintikka htk)
(mhtk : Γ.m ⊆ htk)

instance : decidable_eq info := by tactic.mk_dec_eq_instance

inductive tmodel
| cons : info → list tmodel → list psig → tmodel

instance : decidable_eq tmodel := by tactic.mk_dec_eq_instance

open tmodel

@[simp] def minfo : Π m : tmodel, info
| (cons i l ba) := i

@[simp] def htk : Π m : tmodel, list nnf
| (cons i l ba) := i.htk

def hist : Π m : tmodel, list nnf
| (cons i l ba) := i.Γ.h

@[simp] def msig : Π m : tmodel, sig
| (cons i l ba) := i.Γ.s

@[simp] def manc : Π m : tmodel, list psig
| (cons i l ba) := i.Γ.a

def bhist : Π m : tmodel, list nnf
| (cons i l ba) := i.Γ.b

@[simp] def request : Π m : tmodel, list psig
| (cons i l ba) := ba

@[simp] def proper_request_box : Π m : tmodel, Prop
| (cons i l ba) := ∀ rq : psig, rq ∈ ba → ∀ φ, (box φ ∈ i.htk ∨ box φ ∈ i.Γ.b) → box φ ∈ rq.b

@[simp] def subset_request : Π m : tmodel, Prop
| (cons i l ba) := ba ⊆ i.Γ.a

@[simp] def tmodel_step_bhist : Π m : tmodel, Prop 
| m@(cons i l ba) := ∀ s ∈ l, ∀ φ, box φ ∈ i.Γ.b → box φ ∈ htk s

@[simp] def tmodel_step_box : Π m : tmodel, Prop 
| m@(cons i l ba) := ∀ s ∈ l, ∀ φ, box φ ∈ i.htk → box φ ∈ htk s

-- Can be strenghtened
@[simp] def tmodel_dia : Π m : tmodel, Prop 
| m@(cons i l ba) := ∀ φ, dia φ ∈ i.htk → (∃ rq : psig, rq ∈ ba ∧ rq.d = φ) ∨ ∃ s ∈ l, φ ∈ htk s

@[simp] def child : tmodel → tmodel → bool
| s (cons i l ba) := s ∈ l

inductive tc' {α : Type} (r : α → α → Prop) : α → α → Prop
| base : ∀ a b, r a b → tc' a b
| step : ∀ a b c, r a b → tc' b c → tc' a c

theorem tc'.trans {α : Type} {r : α → α → Prop} {a b c : α} : 
tc' r a b → tc' r b c → tc' r a c :=
begin
intros h₁ h₂,
induction h₁,
apply tc'.step, exact h₁_a_1, exact h₂,
apply tc'.step, exact h₁_a_1, apply h₁_ih, exact h₂
end

def desc : tmodel → tmodel → Prop := tc' (λ s m, child s m)

theorem desc_not_nil : Π c i ba m, m = cons i [] ba → desc c m → false :=
begin
intros c i ba m heq h,
induction h,
{rw heq at h_a_1, simp at h_a_1, exact h_a_1},
{apply h_ih, exact heq}
end

theorem desc_iff_eq_child_aux : Π i₁ i₂ s₁ s₂ l₁ l₂ m₁ m₂ m₃, 
m₁ = cons i₁ l₁ s₁ → m₂ = cons i₂ l₂ s₂ → l₁ = l₂ → 
(desc m₃ m₁ ↔ desc m₃ m₂) :=
begin
intros i₁ i₂ s₁ s₂ l₁ l₂ m₁ m₂ m₃ heq₁ heq₂ heq,
split,
{intro hd, induction hd,
 {rw heq₁ at hd_a_1, simp at hd_a_1,
 rw heq at hd_a_1,
 apply tc'.base, rw heq₂, simp, exact hd_a_1},
 {apply tc'.trans, apply tc'.base, exact hd_a_1, apply hd_ih, exact heq₁}},
{intro hd, induction hd,
 {rw heq₂ at hd_a_1, simp at hd_a_1,
 rw ←heq at hd_a_1,
 apply tc'.base, rw heq₁, simp, exact hd_a_1},
 {apply tc'.trans, apply tc'.base, exact hd_a_1, apply hd_ih, exact heq₂}}
end

theorem eq_desc_of_eq_children {i₁ i₂ s₁ s₂ l c} : 
desc c (cons i₁ l s₁) = desc c (cons i₂ l s₂) :=
begin rw desc_iff_eq_child_aux, repeat {refl} end 

theorem desc_step : Π c i l ba, c ∈ l → desc c (cons i l ba)
| c i [] ba h := absurd h $ list.not_mem_nil _
| c i (hd::tl) ba h := 
begin
constructor,
simp, cases h,
left, exact h, right, exact h
end

theorem desc_ex : Π c i l ba, (∃ m ∈ l, desc c m) → desc c (cons i l ba)
| c i [] ba h := begin rcases h with ⟨w, hmem, hw⟩, exact (absurd hmem $ list.not_mem_nil _) end
| c i (hd::tl) ba h := 
begin
rcases h with ⟨w, hmem, hw⟩,
cases hw,
{apply tc'.step,
swap 3, {exact w},
{exact hw_a_1},
{apply tc'.base, simp, cases hmem, left, exact hmem, right, exact hmem}},
{apply tc'.step, exact hw_a_1, apply tc'.trans, exact hw_a_2, apply tc'.base, simp, exact hmem}
end

theorem ex_desc : Π c i l ba m, m = (cons i l ba) → desc c m → (c ∈ l ∨ ∃ m ∈ l, desc c m) := 
begin
intros c i l ba m heq h,
induction h,
{left, rw heq at h_a_1, simp at h_a_1, exact h_a_1},
{cases h_ih heq,
 {right, split, split, exact h, apply tc'.base, exact h_a_1},
 {rcases h with ⟨w, hmem, hw⟩, right, split, split, exact hmem, apply tc'.step, exact h_a_1, exact hw}}
end

theorem ex_desc' : Π c i l ba, desc c (cons i l ba) → (c ∈ l ∨ ∃ m ∈ l, desc c m) := 
begin intros c i l ba h, apply ex_desc, repeat {refl}, exact h end

@[simp] def tmodel_anc : Π m : tmodel, Prop 
| m@(cons i l ba) := ∀ s rq, desc s m → rq ∈ request s →  
                     (rq ∈ manc m) ∨
                     (∃ d, desc d m ∧ some rq = msig d)

structure ptmodel (m : tmodel) : Prop :=
(bhist : tmodel_step_bhist m)
(sbox : tmodel_step_box m)
(pdia : tmodel_dia m)
(bdia : tmodel_anc m)
(reqb : proper_request_box m)
(sreq : subset_request m)

def global_pt (m : tmodel) := ∀ s, desc s m → ptmodel s

open subtype

def model : Type := {m : tmodel // ptmodel m ∧ global_pt m}

def model' (Γ : sseqt) : Type := {m : tmodel // ptmodel m ∧ global_pt m ∧ (minfo m).Γ = Γ}

def rmodel : Type := {m : tmodel // ptmodel m}

theorem global_property {m : model} {s : tmodel} (h : desc s m.1) : ptmodel s := m.2.2 s h

inductive reach_step : rmodel → rmodel → Prop
| fwd_base (s : rmodel) (i l ba h) : s.1 ∈ l → reach_step ⟨(cons i l ba), h⟩  s
| bwd_base (s : rmodel) (i l ba h) : (∃ rq ∈ ba, some rq = msig s.1) → reach_step ⟨(cons i l ba), h⟩ s

theorem reach_step_box (s₁ s₂ φ) (h₁ : reach_step s₁ s₂) (h₂ : box φ ∈ htk s₁.1) : φ ∈ htk s₂.1 :=
begin
cases h₁,
{cases s₂ with s₂ ps₂,
 cases s₂ with i₂ l₂ sg₂,
 simp,
 have := h₁_h.sbox,
 simp at this, simp at h₂,
 have hmem := this _ h₁_a _ h₂,
 simp at hmem, apply i₂.hhtk.hbox, exact hmem },
{cases s₂ with s₂ ps₂,
 cases s₂ with i₂ l₂ sg₂,
 simp, apply i₂.hhtk.hbox,
 rcases h₁_a with ⟨w,hmem,hw⟩,
 simp at hw,
 apply i₂.mhtk,
 have := i₂.Γ.ps₂,
 rw ←hw at this,
 have hneq : some w ≠ none, 
   {intro heq, contradiction},
 have hsub := this hneq,
 apply hsub,
 have := h₁_h.reqb,
 simp at this, simp at h₂,
 have hc := this w hmem φ (or.inl h₂),
 cases w, 
 dsimp [bsig], exact hc}
end

theorem reach_step_box' (s₁ s₂ φ) (h₁ : reach_step s₁ s₂) (h₂ : box φ ∈ htk s₁.1) : box φ ∈ htk s₂.1 :=
begin
cases h₁,
{cases s₂ with s₂ ps₂,
 cases s₂ with i₂ l₂ sg₂,
 simp,
 have := h₁_h.sbox,
 simp at this, simp at h₂,
 have hmem := this _ h₁_a _ h₂,
 simp at hmem, exact hmem },
{cases s₂ with s₂ ps₂,
 cases s₂ with i₂ l₂ sg₂,
 simp,
 rcases h₁_a with ⟨w,hmem,hw⟩,
 simp at hw,
 apply i₂.mhtk,
 have := i₂.Γ.ps₂,
 rw ←hw at this,
 have hneq : some w ≠ none, 
   {intro heq, contradiction},
 have hsub := this hneq,
 apply hsub,
 have := h₁_h.reqb,
 simp at this, simp at h₂,
 have hc := this w hmem φ (or.inl h₂),
 cases w, 
 dsimp [bsig], exact hc}
end

inductive rtc {α : Type} (r : α → α → Prop) : α → α → Prop
| refl   : Π a, rtc a a
| step   : Π a b c, r a b → rtc b c → rtc a c

theorem rtc.trans {α : Type} {r : α → α → Prop} {a b c : α} : 
rtc r a b → rtc r b c → rtc r a c :=
begin
intros h₁ h₂,
induction h₁,
exact h₂,
apply rtc.step, exact h₁_a_1, apply h₁_ih, exact h₂
end

theorem rtc_step {α : Type} {r : α → α → Prop} {a b : α} : 
r a b → rtc r a b :=
begin
intros h,
apply rtc.step,
exact h,
apply rtc.refl
end

def reach (s₁ s₂ : rmodel) := rtc reach_step s₁ s₂

theorem refl_reach : Π s, reach s s := λ s, rtc.refl _ _

theorem trans_reach : Π s₁ s₂ s₃, reach s₁ s₂ → reach s₂ s₃ → reach s₁ s₃ := λ s₁ s₂ s₃ h₁ h₂, rtc.trans h₁ h₂

@[simp] def frame (m : model) : S4 {x : rmodel // x.1 = m.1 ∨ desc x.1 m.1} := 
{val := λ v s, var v ∈ htk s.1.1, 
 rel := λ s₁ s₂, reach s₁ s₂, 
 refl := λ s, refl_reach s, 
 trans := λ a b c, trans_reach a b c}

@[simp] def frame' {Γ} (m : model' Γ) : S4 {x : rmodel // x.1 = m.1 ∨ desc x.1 m.1} := 
{val := λ v s, var v ∈ htk s.1.1, 
 rel := λ s₁ s₂, reach s₁ s₂, 
 refl := λ s, refl_reach s, 
 trans := λ a b c, trans_reach a b c}

open rtc

theorem reach_box (s₁ s₂ φ) (h₁ : reach s₁ s₂) (h₂ : box φ ∈ htk s₁.1) : φ ∈ htk s₂.1 :=
begin
induction h₁ with m m₁ m₂ m₃ h₁₂ h₂₃ ih, 
{cases m with tm hm, cases tm with i l sg,
simp,
apply i.hhtk.hbox,
simp at h₂, exact h₂},
{apply ih, 
 apply reach_step_box',
 exact h₁₂, exact h₂}
end

theorem reach_step_dia {Γ} (s : rmodel) (rt : model' Γ) (φ) 
(h₁ : desc s.1 rt.1) 
(h₂ : manc rt.1 = []) (h₃ : dia φ ∈ htk s.1) : 
∃ s', reach_step s s' ∧ φ ∈ htk s'.1 ∧ desc s'.1 rt.1 :=
begin
cases s with s ps,
cases s with i l sg,
have := ps.pdia,
simp at this, simp at h₃,
have hc := this _ h₃,
cases hc,
{cases rt with rt prt,
 cases rt with irt lrt sgrt,
 rcases hc with ⟨w, hmem, hw⟩,
 have := prt.1.bdia,
 simp at this, simp at h₁,
 have hcaux := this _ w h₁,
 simp at hcaux,
 have hcc := hcaux hmem,
 simp at h₂,
 cases hcc,
 {rw h₂ at hcc, exfalso, apply list.not_mem_nil, exact hcc},
 {rcases hcc with ⟨m, hml, hmr⟩, 
  have pm := prt.2.1 m hml,
  split, split,
  swap 3, exact ⟨m, pm⟩,
  apply reach_step.bwd_base,
  split, split, exact hmem, simp, exact hmr,
  split,
  {cases m with im lm sgm, simp,
   apply im.mhtk, 
   have := im.Γ.ps₁,
   simp at hmr, rw ←hmr at this,
   have hneq : some w ≠ none, {intro, contradiction},
   have hmem := this hneq, 
   cases w, dsimp [dsig] at hmem,
   rw ←hw, exact hmem_1 },
  {exact hml} } },
{rcases hc with ⟨m, pml, pmr⟩,
 have hdm : desc m rt.1, 
  {apply tc'.trans, apply tc'.base, 
   swap 3, exact (⟨cons i l sg, ps⟩ : rmodel).val, 
   simp, exact pml, exact h₁},
 cases rt with rt prt,
 cases rt with irt lrt sgrt,
 have pm := prt.2.1 m hdm,
 split, split, swap 3,
 exact ⟨m, pm⟩,
 apply reach_step.fwd_base,
 exact pml, split,
 {exact pmr},
 {exact hdm} }
end

theorem reach_dia {Γ} (s : rmodel) (rt : model' Γ) (φ) 
(h₁ : desc s.1 rt.1) 
(h₂ : manc rt.1 = []) (h₃ : dia φ ∈ htk s.1) : 
∃ s', reach s s' ∧ φ ∈ htk s'.1 ∧ desc s'.1 rt.1:=
begin
have := reach_step_dia s rt φ h₁ h₂ h₃,
rcases this with ⟨w, hwl, hwr⟩,
split, split, swap 3, exact w,
apply rtc_step hwl, exact hwr
end

theorem reach_step_dia_root {Γ} (s : rmodel) (rt : model' Γ) (φ) 
(h₁ : s.1 = rt.1) 
(h₂ : manc rt.1 = []) (h₃ : dia φ ∈ htk s.1) : 
∃ s', reach_step s s' ∧ φ ∈ htk s'.1 ∧ desc s'.1 rt.1 :=
begin
cases s with s ps,
cases s with is ls sgs,
have := ps.pdia,
simp at this, simp at h₃,
have hc := this _ h₃,
cases hc,
{have := ps.sreq, simp at this, 
 rcases hc with ⟨w, hmw, hw⟩,
 have hmem := this hmw,
 cases rt with rt prt,
 rw ←h₁ at h₂,
 simp at h₂, rw h₂ at hmem,
 exfalso, apply list.not_mem_nil, exact hmem},
{cases rt with rt prt,
 rcases hc with ⟨w, hwl, hwr⟩,
 have ptw : ptmodel w, 
   {apply prt.2.1, apply tc'.base, simp at h₁, rw ←h₁, simp, exact hwl},
 split, split, swap 3, exact ⟨w, ptw⟩,
 apply reach_step.fwd_base, exact hwl, split, 
 {exact hwr}, 
 {apply tc'.base, simp, simp at h₁, rw ←h₁, simp, exact hwl} }
end

theorem reach_dia_root {Γ} (s : rmodel) (rt : model' Γ) (φ) 
(h₁ : s.1 = rt.1) 
(h₂ : manc rt.1 = []) (h₃ : dia φ ∈ htk s.1) : 
∃ s', reach s s' ∧ φ ∈ htk s'.1 ∧ desc s'.1 rt.1 :=
begin
have := reach_step_dia_root s rt φ h₁ h₂ h₃,
rcases this with ⟨w, hwl, hwr⟩,
split, split, swap 3, exact w,
apply rtc_step hwl, exact hwr
end

theorem good_model {Γ} (m : model' Γ) (hrt : manc m.1 = []): 
Π (s : {x : rmodel // x.1 = m.1 ∨ desc x.1 m.1}) (φ : nnf), 
  φ ∈ htk s.1.1 → force (frame' m) s φ
| s (var n) h   := begin simp, exact h end
| s (neg n) h   := begin 
                     simp, intro hin, 
                     cases s with s ps,
                     cases s with s pts,
                     cases s with i l sg,
                     have := i.hhtk.hno_contra,
                     simp at hin,
                     apply this hin, simp at h, exact h
                   end
| s (and φ ψ) h := begin 
                   split,
                   {apply good_model, 
                   cases s with s ps,
                   cases s with s pts,
                   cases s with i l sg,
                   have := i.hhtk.hand_left,
                   simp, apply this, simp at h, exact h},
                   {apply good_model, 
                   cases s with s ps,
                   cases s with s pts,
                   cases s with i l sg,
                   have := i.hhtk.hand_right,
                   simp, apply this, simp at h, exact h}
                   end
| s (or φ ψ) h  := begin
                   cases s with s ps,
                   cases s with s pts,
                   cases s with i l sg,
                   have := i.hhtk.hor,
                   simp at h,
                   have hc := this h,
                   cases hc,
                   {simp, left, apply good_model, simp, exact hc},
                   {simp, right, apply good_model, simp, exact hc}
                   end
| s (box φ) h   := begin
                   intros m hm,
                   apply good_model,
                   apply reach_box,
                   exact hm,
                   exact h
                   end
| s (dia φ) h   := begin
                   cases s with s ps,
                   cases ps,
                   {simp, simp at h,
                    have := reach_dia_root _ _ _ ps hrt h,
                    rcases this with ⟨s', hs'l, hs'm, hs'r⟩,
                    split, split, 
                    exact hs'l, split, apply good_model, simp,
                    exact hs'm, right, exact hs'r },
                   {simp, simp at h,
                    have := reach_dia _ _ _ ps hrt h,
                    rcases this with ⟨s', hs'l, hs'm, hs'r⟩,
                    split, split, 
                    exact hs'l, split, apply good_model, simp,
                    exact hs'm, right, exact hs'r}
                   end



section
variables (φ ψ : nnf) (Γ₁ Γ₂ Δ Λ: list nnf) {st : Type}
variables (k : S4 st) (s : st)
open list

theorem sat_subset (h₁ : Γ₁ ⊆ Γ₂) (h₂ : sat k s Γ₂) : sat k s Γ₁ :=
λ x hx, h₂ _ (h₁ hx)

theorem sat_sublist (h₁ : Γ₁ <+ Γ₂) (h₂ :sat k s Γ₂) : sat k s Γ₁ := 
sat_subset _ _ _ _ (subset_of_sublist h₁) h₂

theorem sat_append (h₁ : sat k s Γ₁) (h₂ : sat k s Γ₂) : sat k s (Γ₁ ++ Γ₂) :=
begin
  intros φ h, rw mem_append at h, cases h,
  apply h₁ _ h, apply h₂ _ h
end

theorem unsat_contra  {Δ n} : var n ∈ Δ →  neg n ∈ Δ →  unsatisfiable Δ:= 
begin
  intros h₁ h₂, intros v hsat, intros s hsat,
  have := hsat _ h₁, have := hsat _ h₂, simpa
end

theorem unsat_contra_seqt {Δ : sseqt} {n} : var n ∈ Δ.m →  neg n ∈ Δ.m →  unsatisfiable (Δ.m ++ Δ.b):= 
begin
  intros h₁ h₂, intros st m, intros s hsat,
  have := unsat_contra h₁ h₂,
  have := this _ m s,
  apply this,
  apply sat_subset _ _ _ _ _ hsat, 
  simp
end

theorem sat_of_and : force k s (and φ ψ) ↔ (force k s φ) ∧ (force k s ψ) := 
by split; {intro, simpa}

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

theorem sat_and_of_sat_split_seqt {Γ}
        (h₁ : and φ ψ ∈ Δ) 
        (h₂ : sat k s $ (φ :: ψ :: Δ.erase (and φ ψ)++Γ)) : 
        sat k s (Δ++Γ) := 
begin
  intro e, intro he,
  by_cases (e = and φ ψ),
  { rw h, dsimp, split, repeat {apply h₂, simp} },
  { have : e ∈ Δ.erase (and φ ψ) ++ Γ,
      { rw ←erase_append_left, rw mem_erase_of_ne, repeat {assumption} },
    apply h₂, simp [this] }
end

theorem sat_split_of_sat_and_seqt {Γ}
        (h₁ : and φ ψ ∈ Δ) 
        (h₂ : sat k s (Δ++Γ)) : 
        sat k s $ (φ :: ψ :: Δ.erase (and φ ψ)++Γ) := 
begin
  intros e he, rw mem_append at he, cases he,
  have : force k s (and φ ψ), {apply h₂, simp [h₁]}, rw sat_of_and at this, 
  {cases he, 
  {rw he, exact this.left}, 
  {cases he, rw he, exact this.right, apply h₂, rw mem_append, left, apply mem_of_mem_erase he}
  },
  {apply h₂, rw mem_append, right, exact he}
end

theorem unsat_or_of_unsat_split_seqt {Γ}
        (h : or φ ψ ∈ Δ) 
        (h₁ : unsatisfiable $ (φ :: Δ.erase (nnf.or φ ψ)++Γ)) 
        (h₂ : unsatisfiable $ (ψ :: Δ.erase (nnf.or φ ψ)++Γ)) : 
        unsatisfiable $ (Δ++Γ) := 
begin
  intro, intros, intro hsat,
  have := hsat _ (mem_append_left _ h),
  dsimp at this,
  cases this,
  {apply h₁, swap 3, exact k, swap, exact s, intro e, intro he, 
   cases he, rw he, exact this, apply hsat, 
apply mem_of_mem_erase, rw erase_append_left, exact he, exact h},
  {apply h₂, swap 3, exact k, swap, exact s, intro e, intro he, 
   cases he, rw he, exact this, apply hsat, apply mem_of_mem_erase, rw erase_append_left, exact he, exact h}
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

/- S4-specific lemmas -/

theorem force_of_force_box (h : force k s $ box φ) : force k s φ 
:= begin dsimp at h, apply h, apply k.refl end

theorem force_box_box_of_force_box : force k s (box φ) → force k s (box (box φ)) :=
begin
intros h,
simp at h,
simp,
intros s₁ rs₁ s₂ rs₂,
apply h,
apply k.trans,
exact rs₁, exact rs₂
end

theorem unsat_of_unsat_box_new
        (h₁ : box φ ∈ Δ) 
        (h₂ : unsatisfiable $ (φ :: Δ.erase (box φ)) ++ box φ :: Λ) : 
        unsatisfiable (Δ ++ Λ) :=
begin
  intros st k s h,
  apply h₂, swap 3, exact k, swap, exact s,
  intros e he,
  rw [mem_append] at he,
  cases he,
  {cases he, 
    {rw he, apply force_of_force_box, apply h (box φ), simp [h₁]},
    {apply h, rw mem_append, left, apply mem_of_mem_erase he }},
  {cases he, 
    {rw ←he at h₁, apply h, rw mem_append, left, exact h₁},
    {apply h, rw mem_append, right, assumption}}
end

theorem sat_copy_of_sat_box_new
        (h₁ : box φ ∈ Δ) 
        (h₂ : sat k s $ (φ :: Δ.erase (box φ)) ++ box φ :: Λ) : 
        sat k s (Δ ++ Λ) :=
begin
  intros ψ hφ,
  rw mem_append at hφ,
  cases hφ,
  {by_cases heq : ψ = box φ, 
    {rw heq, apply h₂ (box φ), simp}, 
    {have := mem_erase_of_ne heq, rw ←this at hφ, apply h₂, simp, right, left, exact hφ}},
  {apply h₂, simp, repeat {right}, exact hφ}
end

theorem unsat_of_unsat_box_dup
        (h₁ : box φ ∈ Δ)
        (h₃ : unsatisfiable $ (φ :: Δ.erase (box φ)) ++ Λ) : 
        unsatisfiable (Δ ++ Λ) :=
begin
  intros st k s h,
  apply h₃, swap 3, exact k, swap, exact s,
  intros e he,
  cases he,
  {rw he, apply force_of_force_box, apply h (box φ), simp [h₁]},
  {have := mem_append.1 he, cases this, 
   {apply h, apply mem_append_left, apply mem_of_mem_erase this},
   {apply h, apply mem_append_right, exact this}}
end


end

-- theorem build_model : Π Γ (h : model_constructible Γ), model := _
