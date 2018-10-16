import defs
open list

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

theorem split_lt_and {φ ψ} (Γ : list nnf) (h : nnf.and φ ψ ∈ Γ) :
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

theorem split_lt_or_left {φ ψ} (Γ : list nnf) (h : nnf.or φ ψ ∈ Γ) :
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

theorem split_lt_or_right {φ ψ} (Γ : list nnf) (h : nnf.or φ ψ ∈ Γ) :
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
