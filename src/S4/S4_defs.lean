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

instance : decidable_eq sseqt := by tactic.mk_dec_eq_instance

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

def minfo : Π m : tmodel, info
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

def tmodel_step_bhist : Π m : tmodel, Prop 
| m@(cons i l ba) := ∀ s ∈ l, ∀ φ, box φ ∈ i.Γ.b → box φ ∈ htk s

@[simp] def tmodel_step_box : Π m : tmodel, Prop 
| m@(cons i l ba) := ∀ s ∈ l, ∀ φ, box φ ∈ i.htk → box φ ∈ htk s

@[simp] def tmodel_dia : Π m : tmodel, Prop 
| m@(cons i l ba) := ∀ φ, dia φ ∈ i.htk → (∃ rq : psig, rq ∈ ba ∧ rq.d = φ) ∨ ∃ s ∈ l, φ ∈ htk s

@[simp] def pmsig_dia : Π m : tmodel, Prop
| m@(cons i l ba) := Π (h : i.Γ.s ≠ none), dsig i.Γ.s h ∈ i.Γ.m

@[simp] def pmsig_box : Π m : tmodel, Prop
| m@(cons i l ba) := Π (h : i.Γ.s ≠ none), bsig i.Γ.s h ⊆ i.Γ.m

@[simp] def child : tmodel → tmodel → bool
| s (cons i l ba) := s ∈ l

inductive tc' {α : Type} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc' a b
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

@[simp] def tmodel_anc : Π m : tmodel, Prop 
| m@(cons i l ba) := ∀ s rq, desc s m → rq ∈ request s →  
                     (rq ∈ manc m) ∨
                     -- (some rq = msig m) ∨
                     (∃ d, desc d m ∧ some rq = msig d)

structure ptmodel (m : tmodel) : Prop :=
(bhist : tmodel_step_bhist m)
(sbox : tmodel_step_box m)
(pdia : tmodel_dia m)
(bdia : tmodel_anc m)
(psig₁ : pmsig_dia m)
(psig₂ : pmsig_box m)
(reqb : proper_request_box m)
(sreq : subset_request m)

def global_pt (m : tmodel) := ∀ s, desc s m → ptmodel s

open subtype

def model : Type := {m : tmodel // ptmodel m ∧ global_pt m}

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
 have := ps₂.psig₂,
 simp at this, rw ←hw at this,
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
 have := ps₂.psig₂,
 simp at this, rw ←hw at this,
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

def reach (s₁ s₂ : rmodel) := rtc reach_step s₁ s₂

theorem refl_reach : Π s, reach s s := λ s, rtc.refl _ _

theorem trans_reach : Π s₁ s₂ s₃, reach s₁ s₂ → reach s₂ s₃ → reach s₁ s₃ := λ s₁ s₂ s₃ h₁ h₂, rtc.trans h₁ h₂

def frame : Π m : model, S4 {x : rmodel // x.1 = m.1 ∨ desc x.1 m.1} 
| m@⟨(cons i l ba), p⟩ := {val := λ v s, var v ∈ htk s.1.1, 
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

theorem reach_dia (s : rmodel) (rt : model) (φ) 
(h₁ : desc s.1 rt.1) 
(h₂ : manc rt.1 = []) (h₃ : dia φ ∈ htk s.1) : 
∃ s', reach_step s s' ∧ φ ∈ htk s'.1 :=
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
  have pm := prt.2 m hml,
  split, split,
  swap 3, exact ⟨m, pm⟩,
  apply reach_step.bwd_base,
  split, split, exact hmem, simp, exact hmr,
  cases m with im lm sgm, simp,
  apply im.mhtk, 
  have := pm.psig₁,
  simp at this, 
  simp at hmr, rw ←hmr at this,
  have hneq : some w ≠ none, {intro, contradiction},
  have hmem := this hneq, 
  cases w, dsimp [dsig] at hmem,
  rw ←hw, exact hmem_1 } },
{rcases hc with ⟨m, pml, pmr⟩,
 have hdm : desc m rt.1, 
  {apply tc'.trans, apply tc'.base, 
   swap 3, exact (⟨cons i l sg, ps⟩ : rmodel).val, 
   simp, exact pml, exact h₁},
 cases rt with rt prt,
 cases rt with irt lrt sgrt,
 have pm := prt.2 m hdm,
 split, split, swap 3,
 exact ⟨m, pm⟩,
 apply reach_step.fwd_base,
 exact pml, exact pmr}
end
