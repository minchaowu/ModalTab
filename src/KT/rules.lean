import .semantics
open nnf subtype list

-- inductive node (Γ : list nnf) : Type
-- | closed : Π m, unsatisfiable Γ → pmark Γ m → node
-- | open_  : {s // sat builder s Γ} → node

inductive node (Γ : seqt) : Type
| closed : unsatisfiable (Γ.main ++ Γ.hdld) → node
-- | open_ : {s // sat }
