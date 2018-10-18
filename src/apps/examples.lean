import .topo_translation ..K.jump

open nnf

def boom : nnf := dia (and (var 1) (neg 1))

-- #eval is_sat [boom]

-- #check tableau [boom]

def topo_fact_of (φ : nnf) : psum (∀ (α) (tm : topo_model α) s, ¬ topo_force tm s φ) unit :=
match tableau [φ] with
| node.closed _ h _ := psum.inl $ not_topo_force_of_unsat h
| node.open_ _ := psum.inr ()
end
