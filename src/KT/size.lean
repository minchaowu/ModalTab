import .KT_defs
open nnf prod

namespace prod

universe u

def measure_lex {α : Sort u} : (α → ℕ × ℕ) → α → α → Prop :=
inv_image $ lex (<) (<)

def measure_lex_wf {α : Sort u} (f : α → ℕ × ℕ) : well_founded (measure_lex f) :=
inv_image.wf f (lex_wf nat.lt_wf nat.lt_wf)

end prod

section
-- replace these by mathlib lemmas
universe u
variables {α : Type u} [decidable_linear_order α]

lemma max_absorb_left {a b : α} : max (max a b) a = max a b := 
begin by_cases h : a ≤ b, {rw max_eq_right h, rw max_eq_left h}, {rw max_eq_left (le_of_not_le h), apply max_self} end

lemma max_absorb_right {a b : α} : max (max a b) b = max a b := 
begin by_cases h : a ≤ b, {rw max_eq_right h, apply max_self}, repeat {rw max_eq_left (le_of_not_le h)} end

lemma le_max_of_le_left {a b c : α} (h : c ≤ a) : c ≤ max a b := 
le_trans h $ le_max_left _ _

lemma le_max_of_le_right {a b c : α} (h : c ≤ b) : c ≤ max a b := 
le_trans h $ le_max_right _ _

lemma lt_max_of_lt_left {a b c : α} (h : c < a) : c < max a b := 
lt_of_lt_of_le h $ le_max_left _ _

lemma lt_max_of_lt_right {a b c : α} (h : c < b) : c < max a b := 
lt_of_lt_of_le h $ le_max_right _ _

lemma or_of_max {a b : α} : max a b = a ∨ max a b = b := 
begin by_cases h : a ≤ b, {right, rw max_eq_right h}, {left, rw max_eq_left (le_of_not_le h)} end

lemma max_le_of_le {a b c d : α} (h₁ : a ≤ c) (h₂ : b ≤ d) : max a b ≤ max c d :=
max_le (le_max_of_le_left h₁) (le_max_of_le_right h₂)

lemma max_lt_of_lt {a b c d : α} (h₁ : a < c) (h₂ : b < d) : max a b < max c d :=
max_lt (lt_max_of_lt_left h₁) (lt_max_of_lt_right h₂)

end

namespace list
universes u
variables {α : Type u} [inhabited α] [decidable_linear_order α]

def maximum (l : list α) : α := l.foldr max l.head

theorem le_of_foldr_max : Π {a b : α} {l}, a ∈ l → a ≤ foldr max b l
| a b [] h := absurd h $ not_mem_nil _
| a b (hd::tl) h := 
begin 
  cases h, 
  { simp [h, le_max_left] }, 
  { simp [le_max_of_le_right, le_of_foldr_max h] } 
end

theorem mem_of_foldr_max : Π {a : α} {l}, foldr max a l ∈ a :: l
| a [] := by simp
| a (hd::tl) := 
begin
  simp only [foldr_cons],
  have h := by exact @or_of_max _ _ hd (foldr max a tl),
  cases h, 
  { simp [h] }, 
  { rw h, 
    have hmem := @mem_of_foldr_max a tl, 
    cases hmem, { simp [hmem] }, { right, right, exact hmem } }
end

theorem mem_maximum : Π {l : list α}, l ≠ [] →  maximum l ∈ l
| [] h := by contradiction
| (hd::tl) h := 
begin
  dsimp [maximum],
  have hc := by exact @or_of_max _ _ hd (foldr max hd tl),
  cases hc, { simp [hc] }, { simp [hc, mem_of_foldr_max] }
end

theorem le_maximum_of_mem : Π {a : α} {l}, a ∈ l → a ≤ maximum l
| a [] h := absurd h $ not_mem_nil _
| a (hd::tl) h := 
begin
  cases h,
  { rw h, apply le_of_foldr_max, simp },
  { dsimp [maximum], apply le_max_of_le_right, apply le_of_foldr_max h }
end

def maximum_cons : Π {a : α} {l}, l ≠ [] → maximum (a :: l) = max a (maximum l)
| a [] h := by contradiction
| a (hd::tl) h := 
begin
  apply le_antisymm,
  { have : a :: hd :: tl ≠ [], { simp [h] },
    have hle := mem_maximum this, 
    cases hle, 
    { rw hle, apply le_max_left }, 
    { apply le_max_of_le_right, apply le_maximum_of_mem, exact hle } },
  { have hc := by exact @or_of_max _ _ a (maximum $ hd :: tl),
    cases hc, 
    { rw hc, apply le_maximum_of_mem, simp }, 
    { rw hc, apply le_maximum_of_mem, right, exact mem_maximum h } }
end

end list

open list

@[simp] def count_modal : nnf → ℕ 
| (var n)    := 0
| (neg n)    := 0
| (and φ ψ)  := count_modal φ + count_modal ψ
| (or φ ψ)   := count_modal φ + count_modal ψ
| (box φ)    := count_modal φ + 1
| (dia φ)    := count_modal φ + 1

def modal_degree (Γ : list nnf) : ℕ := maximum $ Γ.map count_modal

theorem cons_degree : Π (φ : nnf) (Γ : list nnf), 
modal_degree (φ :: Γ) = max (count_modal φ) (modal_degree Γ) 
| φ [] := begin dsimp [modal_degree, maximum], simp, rw max_eq_left, apply zero_le end
| φ (hd::tl) := begin simp only [modal_degree], apply maximum_cons, simp end

theorem mem_degree : Π (φ : nnf) (Γ : list nnf), φ ∈ Γ → count_modal φ ≤ modal_degree Γ
| φ [] h := absurd h $ list.not_mem_nil _
| φ (hd::tl) h := 
begin
cases h,
{rw h, rw cons_degree, apply le_max_left},
{rw cons_degree, apply le_max_of_le_right, apply mem_degree, exact h}
end

@[simp] def seqt_size (s : seqt) : ℕ × ℕ := (modal_degree $ s.main ++ s.hdld, node_size s.main) 
