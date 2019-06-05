/-
Copyright (c) 2018-2019 Minchao Wu. All rights reserved.
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

def box_only_nil : box_only [] := 
{no_var := λ n hn, absurd hn $ list.not_mem_nil _, 
no_neg := λ n hn, absurd hn $ list.not_mem_nil _, 
no_and := λ φ ψ hn, absurd hn $ list.not_mem_nil _, 
no_or := λ φ ψ hn, absurd hn $ list.not_mem_nil _, 
no_dia := λ n hn, absurd hn $ list.not_mem_nil _}

def cons_box_only {φ Γ} (h : box_only Γ) : box_only (box φ :: Γ) := 
{no_var := begin intros n hn, cases hn, contradiction, apply h.no_var, exact hn end, 
no_neg := begin intros n hn, cases hn, contradiction, apply h.no_neg, exact hn end, 
no_and := begin intros ψ₁ ψ₂ hψ, cases hψ, contradiction, apply h.no_and, exact hψ end, 
no_or := begin intros ψ₁ ψ₂ hψ, cases hψ, contradiction, apply h.no_or, exact hψ end, 
no_dia := begin intros n hn, cases hn, contradiction, apply h.no_dia, exact hn end}

def box_only_ex : Π {φ Γ} (h₁ : box_only Γ) (h₂ : φ ∈ Γ), ∃ ψ, φ = box ψ 
| (var n) Γ h₁ h₂   := begin exfalso, apply h₁.no_var, exact h₂ end
| (neg n) Γ h₁ h₂   := begin exfalso, apply h₁.no_neg, exact h₂ end
| (and φ ψ) Γ h₁ h₂ := begin exfalso, apply h₁.no_and, exact h₂ end
| (or φ ψ) Γ h₁ h₂  := begin exfalso, apply h₁.no_or, exact h₂ end
| (box φ) Γ h₁ h₂   := ⟨φ, rfl⟩
| (dia φ) Γ h₁ h₂   := begin exfalso, apply h₁.no_dia, exact h₂ end

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
(val : ℕ → states → Prop)
(rel : states → states → Prop)

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

@[simp] def nnf.closure : list nnf → list nnf
| [] := []
| (hd::tl) := sub_nnf hd ++ nnf.closure tl

theorem mem_closure_self : Π Γ : list nnf, Γ ⊆ nnf.closure Γ
| [] := λ x h, absurd h $ list.not_mem_nil _
| (hd::tl) := 
begin 
  intros x hx, cases hx, 
  {rw hx, simp, left, apply mem_sub_nnf_self},
  {simp, right, apply mem_closure_self, exact hx} 
end

theorem mem_closure_and {φ ψ : nnf} : Π Γ : list nnf, and φ ψ ∈ nnf.closure Γ → φ ∈ nnf.closure Γ ∧ ψ ∈ nnf.closure Γ
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

theorem mem_closure_or {φ ψ : nnf} : Π Γ : list nnf, or φ ψ ∈ nnf.closure Γ → φ ∈ nnf.closure Γ ∧ ψ ∈ nnf.closure Γ
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

theorem mem_closure_box {φ : nnf} : Π Γ : list nnf, box φ ∈ nnf.closure Γ → φ ∈ nnf.closure Γ
| [] h := absurd h $ list.not_mem_nil _
| (hd::tl) h := 
begin
simp at h,
cases h,
{simp, left, apply mem_sub_nnf_box _ h},
{simp, right, apply mem_closure_box _ h}
end

theorem mem_closure_dia {φ : nnf} : Π Γ : list nnf, dia φ ∈ nnf.closure Γ → φ ∈ nnf.closure Γ
| [] h := absurd h $ list.not_mem_nil _
| (hd::tl) h := 
begin
simp at h,
cases h,
{simp, left, apply mem_sub_nnf_dia _ h},
{simp, right, apply mem_closure_dia _ h}
end

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
