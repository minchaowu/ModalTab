import .KT_defs algebra.order_functions
open nnf prod

namespace prod

universe u

def measure_lex {α : Sort u} : (α → ℕ × ℕ) → α → α → Prop :=
inv_image $ lex (<) (<)

def measure_lex_wf {α : Sort u} (f : α → ℕ × ℕ) : well_founded (measure_lex f) :=
inv_image.wf f (lex_wf nat.lt_wf nat.lt_wf)

end prod

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
  { simp [le_max_right_of_le, le_of_foldr_max h] } 
end

theorem mem_of_foldr_max : Π {a : α} {l}, foldr max a l ∈ a :: l
| a [] := by simp
| a (hd::tl) := 
begin
  simp only [foldr_cons],
  have h := by exact @max_choice _ _ hd (foldr max a tl),
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
  have hc := by exact @max_choice _ _ hd (foldr max hd tl),
  cases hc, { simp [hc] }, { simp [hc, mem_of_foldr_max] }
end

theorem le_maximum_of_mem : Π {a : α} {l}, a ∈ l → a ≤ maximum l
| a [] h := absurd h $ not_mem_nil _
| a (hd::tl) h := 
begin
  cases h,
  { rw h, apply le_of_foldr_max, simp },
  { dsimp [maximum], apply le_max_right_of_le, apply le_of_foldr_max h }
end

def maximum_cons : Π {a : α} {l}, l ≠ [] → maximum (a :: l) = max a (maximum l)
| a [] h := by contradiction
| a (hd::tl) h := 
begin
  apply le_antisymm,
  { have : a :: hd :: tl ≠ [], { simp [h] },
    have hle := mem_maximum this, 
    cases hle, 
    { simp [hle, le_max_left] }, 
    { apply le_max_right_of_le, apply le_maximum_of_mem, exact hle } },
  { have hc := by exact @max_choice _ _ a (maximum $ hd :: tl),
    cases hc, 
    { simp [hc, le_maximum_of_mem] }, 
    { simp [hc, le_maximum_of_mem, mem_maximum h] } }
end

@[simp] def maximum_singleton : Π {a : α}, maximum [a] = a := by simp [maximum]

section
variables hdf : ∀ {a}, default α ≤ a
include hdf

def maximum_nil : Π {a : α}, max a (maximum []) = a :=
λ a, by dsimp [maximum]; apply max_eq_left; apply hdf

def maximum_cons_default : Π {a : α} {l}, maximum (a :: l) = max a (maximum l)
| a [] := begin rw maximum_nil, simp, assumption end
| a (hd::tl) := 
begin
  apply le_antisymm,
  { have : a :: hd :: tl ≠ [], { simp },
    have hle := mem_maximum this, 
    cases hle, 
    { rw hle, apply le_max_left }, 
    { apply le_max_right_of_le, apply le_maximum_of_mem, exact hle } },
  { have hc := by exact @max_choice _ _ a (maximum $ hd :: tl),
    cases hc, 
    { rw hc, apply le_maximum_of_mem, simp }, 
    { rw hc, apply le_maximum_of_mem, right, 
      have : hd :: tl ≠ [], { simp }, 
      exact mem_maximum this } }
end

def maximum_erase : Π {a : α} {l}, a ∈ l → maximum l = max a (maximum $ l.erase a)
| a [] h := absurd h $ not_mem_nil _
| a (hd::tl) h := 
begin
  by_cases heq : a = hd,
  { rw heq, simp, apply maximum_cons_default, assumption },
  { rw maximum_cons_default @hdf,
    rw maximum_erase (mem_of_ne_of_mem heq h), 
    rw erase_cons_tail, 
    rw maximum_cons_default @hdf, 
    repeat {rw ←max_assoc},
    simp [max_comm], 
    intro hc, rw hc at heq, contradiction }
end

def maximum_subset : Π {l₁ l₂ : list α}, l₁ ⊆ l₂ → maximum l₁ ≤ maximum l₂
| [] l₂ h := by apply hdf
| (hd::tl) l₂ h := 
begin
  rw maximum_cons_default, apply max_le,
  { apply le_maximum_of_mem, apply h, simp },
  { apply maximum_subset, rw cons_subset at h, exact h.right },
  assumption
end

def maximum_sublist {l₁ l₂ : list α} (h : l₁ <+ l₂) : maximum l₁ ≤ maximum l₂ :=
maximum_subset (by assumption) (subset_of_sublist h)

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

theorem le_of_mem_degree : Π (φ : nnf) (Γ : list nnf), φ ∈ Γ → count_modal φ ≤ modal_degree Γ
| φ [] h := absurd h $ list.not_mem_nil _
| φ (hd::tl) h := 
begin
  cases h,
  {rw h, rw cons_degree, apply le_max_left},
  {rw cons_degree, apply le_max_right_of_le, apply le_of_mem_degree, exact h}
end

theorem le_degree_of_subset : Π {l₁ l₂ : list nnf}, l₁ ⊆ l₂ → 
modal_degree l₁ ≤ modal_degree l₂
:=
begin
  intros,
  dsimp [modal_degree],
  apply maximum_subset,
  {exact zero_le},
  {apply map_subset _ a}
end

@[simp] def seqt_size (s : seqt) : ℕ × ℕ := (modal_degree $ s.main ++ s.hdld, node_size s.main) 

instance : has_well_founded seqt := 
⟨ prod.measure_lex seqt_size, prod.measure_lex_wf seqt_size ⟩

lemma size_erase_add_eq_size_sum {φ} : Π (Γ : list nnf) (h : φ ∈ Γ), node_size (Γ.erase φ) + sizeof φ = node_size Γ
| [] h := absurd h $ not_mem_nil _
| (hd :: tl) h := 
begin
  by_cases eq : φ = hd,
  {dsimp [list.erase], rw if_pos, rw eq, apply add_comm, rw eq},
  {dsimp [list.erase], rw if_neg, dsimp, rw [add_assoc],   have : node_size (list.erase tl φ) + sizeof φ = node_size tl,
    {apply size_erase_add_eq_size_sum, cases h, contradiction, assumption},
    rw this, intro h', rw h' at eq, contradiction}
end

theorem split_lt_and_size {φ ψ} (Γ : list nnf) (h : nnf.and φ ψ ∈ Γ) :
node_size (φ :: ψ :: Γ.erase (nnf.and φ ψ)) < node_size Γ := 
begin
  dsimp [node_size],
  rw ←size_erase_add_eq_size_sum Γ,
  swap, exact h,
  rw [←add_assoc, add_comm],
  apply add_lt_add_left, dsimp [sizeof, has_sizeof.sizeof, nnf.sizeof],
  rw [add_assoc],
  rw [nat.one_add],
  apply nat.lt_succ_self 
end

theorem split_le_and_degree {φ ψ} (Γ : list nnf) (h : nnf.and φ ψ ∈ Γ) :
modal_degree (φ :: ψ :: Γ.erase (nnf.and φ ψ)) ≤ modal_degree Γ :=
begin
  rw cons_degree, rw cons_degree,
  {rw ←max_assoc, apply max_le, 
  {apply max_le, 
  repeat {apply le_trans, swap 3, exact count_modal (and φ ψ), simp, apply le_of_mem_degree _ _ h}}, 
  {apply le_degree_of_subset, apply erase_subset} }
end

theorem split_lt_and_seqt {φ ψ} (Γ : seqt) (h : nnf.and φ ψ ∈ Γ.main) :
prod.measure_lex seqt_size 
(and_child Γ h) Γ :=
begin
  have hmem : and φ ψ ∈ Γ.main ++ Γ.hdld, {apply mem_append_left _ h},
  have := lt_or_eq_of_le (split_le_and_degree _ hmem),
  cases this,
  {left, 
  simp only [seqt_size, and_child],  rw erase_append_left at this, rw cons_append, rw cons_append, exact this, exact h
  },
  {dsimp only [prod.measure_lex, inv_image, seqt_size], rw [erase_append_left _ h] at this, rw ←this, right,
   apply split_lt_and_size _ h}
end

theorem split_lt_or_size_left {φ ψ} (Γ : list nnf) (h : nnf.or φ ψ ∈ Γ) :
node_size (φ :: Γ.erase (nnf.or φ ψ)) < node_size Γ := 
begin
  dsimp,
  rw ←size_erase_add_eq_size_sum Γ,
  swap, exact h,
  rw [add_comm],
  apply add_lt_add_left, dsimp [sizeof, has_sizeof.sizeof, nnf.sizeof],
  rw [add_comm, ←add_assoc],
  apply nat.lt_add_of_pos_left,
  apply nat.succ_pos
end

theorem split_lt_or_size_right {φ ψ} (Γ : list nnf) (h : nnf.or φ ψ ∈ Γ) :
node_size (ψ :: Γ.erase (nnf.or φ ψ)) < node_size Γ := 
begin
  dsimp,
  rw ←size_erase_add_eq_size_sum Γ,
  swap, exact h,
  rw [add_comm],
  apply add_lt_add_left, dsimp [sizeof, has_sizeof.sizeof, nnf.sizeof],
  apply nat.lt_add_of_pos_left,
  rw nat.one_add,
  apply nat.succ_pos
end

theorem split_le_or_degree_left {φ ψ} (Γ : list nnf) (h : nnf.or φ ψ ∈ Γ) :
modal_degree (φ :: Γ.erase (nnf.or φ ψ)) ≤ modal_degree Γ :=
begin
  rw cons_degree,
  {apply max_le, 
  -- works even when exact count_modal (and φ ψ). How smart `apply` is?
  repeat {apply le_trans, swap 3, exact count_modal (or φ ψ), simp, apply le_of_mem_degree (nnf.or φ ψ) _ h}, 
  {apply le_degree_of_subset, apply erase_subset}}
end

theorem split_le_or_degree_right {φ ψ} (Γ : list nnf) (h : nnf.or φ ψ ∈ Γ) :
modal_degree (ψ :: Γ.erase (nnf.or φ ψ)) ≤ modal_degree Γ :=
begin
  rw cons_degree,
  {apply max_le, 
  repeat {apply le_trans, swap 3, exact count_modal (or φ ψ), simp, apply le_of_mem_degree (nnf.or φ ψ) _ h},
  {apply le_degree_of_subset, apply erase_subset}}
end

theorem split_lt_or_seqt_left {φ ψ} (Γ : seqt) (h : nnf.or φ ψ ∈ Γ.main) :
prod.measure_lex seqt_size (or_child_left Γ h) Γ :=
begin
  have hmem : or φ ψ ∈ Γ.main ++ Γ.hdld, {apply mem_append_left _ h},
  have := lt_or_eq_of_le (split_le_or_degree_left _ hmem),
  cases this,
  {left, simp only [seqt_size, or_child_left],  rw erase_append_left at this, rw cons_append, exact this, exact h},
  {dsimp only [prod.measure_lex, inv_image, seqt_size], rw [erase_append_left _ h] at this, rw ←this, right,
   apply split_lt_or_size_left _ h}
end

theorem split_lt_or_seqt_right {φ ψ} (Γ : seqt) (h : nnf.or φ ψ ∈ Γ.main) :
prod.measure_lex seqt_size (or_child_right Γ h) Γ :=
begin
  have hmem : or φ ψ ∈ Γ.main ++ Γ.hdld, {apply mem_append_left _ h},
  have := lt_or_eq_of_le (split_le_or_degree_right _ hmem),
  cases this,
  {left, simp only [seqt_size, or_child_right],  rw erase_append_left at this, rw cons_append, exact this, exact h},
  {dsimp only [prod.measure_lex, inv_image, seqt_size], rw [erase_append_left _ h] at this, rw ←this, right,
   apply split_lt_or_size_right _ h}
end

theorem copy_lt_size {φ} (Γ : list nnf) (h : nnf.box φ ∈ Γ) :
node_size (φ :: Γ.erase (nnf.box φ)) < node_size Γ := 
begin
  dsimp [node_size],
  rw ←size_erase_add_eq_size_sum Γ,
  swap, exact h, 
  rw [add_comm], simp [sizeof,has_sizeof.sizeof, nnf.sizeof], 
  apply nat.lt_succ_self 
end

theorem copy_eq_degree {φ} (Γ Λ: list nnf) (h : nnf.box φ ∈ Γ) :
modal_degree (φ :: Γ.erase (nnf.box φ) ++ (box φ :: Λ)) = modal_degree (Γ ++ Λ) :=
begin
  rw cons_append, rw cons_degree,
  have : count_modal φ ≤ count_modal (box φ), {simp},
  have : count_modal φ ≤ (modal_degree (list.erase Γ (box φ) ++ box φ :: Λ)), {apply le_trans, exact this, apply le_of_mem_degree, simp},
  have heq := max_eq_right this, 
  rw heq,
  apply nat.le_antisymm,
  {apply le_degree_of_subset, intros x hx, rw mem_append at hx, 
    cases hx, 
    {rw mem_append, left, apply mem_of_mem_erase hx},
    {cases hx, rw mem_append, left, rw ←hx at h, exact h, rw mem_append, right, exact hx}},
  {apply le_degree_of_subset, intros x hx, rw mem_append at hx, 
    cases hx,
    {rw mem_append, by_cases heq : x = box φ, 
      {right, simp [heq]}, 
      {left, rw mem_erase_of_ne heq, exact hx}},
    {rw mem_append, right, simp [hx]} }
end

theorem copy_lt_seqt {φ} (Γ : seqt) (h : nnf.box φ ∈ Γ.main) :
prod.measure_lex seqt_size (box_child Γ h) Γ := 
begin
  have hmem : box φ ∈ Γ.main ++ Γ.hdld, {apply mem_append_left _ h},
  dsimp only [prod.measure_lex, inv_image, seqt_size, box_child], 
  rw [copy_eq_degree], right, apply copy_lt_size,
  repeat {assumption}
end
