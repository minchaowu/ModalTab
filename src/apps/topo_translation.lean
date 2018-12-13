import .topological_semantics ..K.semantics
open nnf

-- local attribute [instance] classical.prop_decidable

@[simp] def topo_to_kripke {α : Type} (tm : topo_model α) : kripke α := 
{ rel := λ s t, s ∈ @closure _ tm.to_topological_space {t},
  val := λ n s, tm.v n s }

theorem trans_force_left {α : Type} {tm : topo_model α} : Π {s} {φ : nnf}, (topo_force tm s φ) → force (topo_to_kripke tm) s φ
| s (var n)   h := by dsimp at h; simp [h]
| s (neg n)   h := by dsimp at h; simp [h]
| s (and φ ψ) h := begin cases h with l r, split, apply trans_force_left l, apply trans_force_left r end
| s (or φ ψ)  h := begin cases h, left, apply trans_force_left h, right, apply trans_force_left h end
| s (box φ)   h := 
begin
  rcases h with ⟨w, hw, hmem⟩,
  intros s' hs',
  apply trans_force_left,
  apply hw.2,
  rw ←set.inter_singleton_ne_empty,
  have := (@mem_closure_iff _ tm.to_topological_space _ _).1,
  swap 3, exact {s'}, apply this, simpa using hs',
  exact hw.1, exact hmem
end
| s (dia φ)   h := 
begin
  let ts := tm.to_topological_space, 
  let o := ⋂₀ {x : set α | s ∈ x ∧ @is_open _ ts x},
  have openo: @is_open _ ts o, 
    { apply tm.is_alex, intros, exact H.2 },
  have hmem : s ∈ o,
    { rw set.mem_sInter, intros, exact H.1 },
  have := (@mem_closure_iff _ tm.to_topological_space _ _).1 h o openo hmem,
  have ex := set.exists_mem_of_ne_empty this,
  cases ex with w hw, dsimp,
  split, split, swap 3, 
  { exact w },
  rw (@mem_closure_iff _ tm.to_topological_space _ _),
  { --apply to_bool_true,
    intros o' hopen' hmem',
    have : o ⊆ o',
      { intro x, intro hx, rw set.mem_sInter at hx, apply hx, split, repeat {assumption} },
  rw set.inter_singleton_ne_empty,
  apply this hw.1 },
  { exact trans_force_left hw.2 }
end

theorem sat_of_topo_sat {Γ : list nnf} 
{α : Type} (tm : topo_model α) (s) (h : topo_sat tm s Γ) : 
sat (topo_to_kripke tm) s Γ := λ φ hφ, trans_force_left $ h φ hφ

theorem unsat_topo_of_unsat {Γ : list nnf} : unsatisfiable Γ → topo_unsatisfiable Γ := 
λ h, (λ α tm s hsat, @h _ (topo_to_kripke tm) s (sat_of_topo_sat _ _ hsat))

def not_topo_force_of_unsat {φ} : unsatisfiable [φ] → ∀ (α) (tm : topo_model α) s, ¬ topo_force tm s φ := 
λ h, topo_unsat_singleton $ unsat_topo_of_unsat h

