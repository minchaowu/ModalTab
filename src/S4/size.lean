import .S4_defs .data
open nnf prod list

namespace prod

universe u

def measure_lex {α : Sort u} : (α → ℕ × ℕ) → α → α → Prop :=
inv_image $ lex (<) (<)

def measure_lex' {α : Sort u} : (α → ℕ × ℕ × ℕ) → α → α → Prop :=
inv_image $ lex (<) (measure_lex (λ x, x))

def measure_lex_wf {α : Sort u} (f : α → ℕ × ℕ) : well_founded (measure_lex f) :=
inv_image.wf f (lex_wf nat.lt_wf nat.lt_wf)

def measure_lex_wf' {α : Sort u} (f : α → ℕ × ℕ × ℕ) : well_founded (measure_lex' f) :=
inv_image.wf f (lex_wf nat.lt_wf (measure_lex_wf (λ x, x)))

end prod

def sseqt_size (s : sseqt) : ℕ × ℕ × ℕ := 
((closure s.goal).length - s.b.length, 
 (closure s.goal).length - s.h.length, 
 node_size s.m)

instance : has_well_founded sseqt := 
⟨prod.measure_lex' sseqt_size, prod.measure_lex_wf' sseqt_size⟩

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

theorem split_lt_and_seqt {φ ψ} (Γ : sseqt) (h : nnf.and φ ψ ∈ Γ.m) :
prod.measure_lex' sseqt_size 
(and_child Γ h) Γ :=
begin
  right, right,
  simp only [and_child],
  apply split_lt_and_size _ h
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

theorem split_lt_or_seqt_left {φ ψ} (Γ : sseqt) (h : nnf.or φ ψ ∈ Γ.m) :
prod.measure_lex' sseqt_size (or_child_left Γ h) Γ :=
begin
  right, right,
  simp only [or_child_left],
  apply split_lt_or_size_left _ h
end

theorem split_lt_or_seqt_right {φ ψ} (Γ : sseqt) (h : nnf.or φ ψ ∈ Γ.m) :
prod.measure_lex' sseqt_size (or_child_right Γ h) Γ :=
begin
  right, right,
  simp only [or_child_right],
  apply split_lt_or_size_right _ h
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

theorem copy_lt_seqt {φ} (Γ : sseqt) (h : nnf.box φ ∈ Γ.m) :
prod.measure_lex' sseqt_size (box_child Γ h) Γ := 
begin
  right, right,
  simp only [box_child],
  apply copy_lt_size _ h
end

theorem box_new_lt_seqt {φ} (Γ : sseqt) 
(h₁ : nnf.box φ ∈ Γ.m) (h₂ : nnf.box φ ∉ Γ.b) :
prod.measure_lex' sseqt_size (box_child_new Γ h₁ h₂) Γ := 
begin
  left,
  apply length_sub_lt_of_nodup_subperm,
  {dsimp [box_child_new], exact Γ.spb},
  {dsimp [box_child_new], apply Γ.sbm, exact h₁},
  {exact h₂},
  {exact Γ.ndb}
end
