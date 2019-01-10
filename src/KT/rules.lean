import .semantics
open nnf subtype list

-- inductive node (Γ : list nnf) : Type
-- | closed : Π m, unsatisfiable Γ → pmark Γ m → node
-- | open_  : {s // sat builder s Γ} → node

inductive node (Γ : seqt) : Type
| closed : unsatisfiable (Γ.main ++ Γ.hdld) → node
| open_ : {s // sat builder s (Γ.main ++ Γ.hdld)} → node

open node

def contra_rule_seqt {Δ : seqt} {n} (h : var n ∈ Δ.main ∧ neg n ∈ Δ.main) : node Δ := 
begin
  left,
  {exact unsat_contra_seqt h.1 h.2}
end

def and_rule_seqt {Γ Δ : seqt} (i : and_instance_seqt Γ Δ) : node Δ → node Γ
| (closed h) := begin 
                      left, 
                      {apply unsat_of_closed_and, repeat {assumption}}, 
                    end

| (open_ w)  := begin
                  right,
                  clear and_rule,
                  cases i with φ ψ h,
                  constructor,
                  exact sat_and_of_sat_split _ _ _ _ _ h w.2
                end
