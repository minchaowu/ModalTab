import .semantics analysis.topology.topological_space
open nnf

structure topo_model (α : Type) extends topological_space α := 
(v : ℕ → set α)
(is_alex : ∀s, (∀t∈s, is_open t) → is_open (⋂₀ s))

@[simp] def topo_force {α : Type} (tm : topo_model α) : α → nnf → Prop
| s (var n)    := tm.v n s
| s (neg n)    := ¬ tm.v n s
| s (and φ ψ)  := topo_force s φ ∧ topo_force s ψ
| s (or φ ψ)   := topo_force s φ ∨ topo_force s ψ
| s (box φ)    := @interior _ tm.to_topological_space (λ a, topo_force a φ) s
| s (dia φ)    := @closure _ tm.to_topological_space (λ a, topo_force a φ) s

def topo_sat {α : Type} (tm : topo_model α) (s) (Γ : list nnf) : Prop := ∀ φ ∈ Γ, topo_force tm s φ


