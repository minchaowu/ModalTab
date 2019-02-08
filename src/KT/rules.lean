import .semantics
open nnf subtype list

-- TODO: we could redefine satisfiability.
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
                  {apply unsat_of_closed_and_seqt, repeat {assumption}}, 
                end

| (open_ w)  := begin
                  right,
                  clear and_rule_seqt,
                  cases i with φ ψ h,
                  constructor,
                  exact sat_and_of_sat_split_seqt _ _ _ _ _ h w.2
                end

def or_rule_seqt {Γ₁ Γ₂ Δ} (i : or_instance_seqt Δ Γ₁ Γ₂) : 
            node Γ₁ → node Γ₂ → node Δ
| (open_ w) _ := begin
                   right,
                   clear or_rule_seqt,
                   cases i,
                   constructor,
                   apply sat_or_of_sat_split_left,
                   apply subset_append_left,
                   assumption,
                   apply sat_subset, swap, exact w.2,
                   rw erase_append_left _ i_h,
                   rw ←cons_append, simp
                 end
| _ (open_ w) := begin
                   right,
                   clear or_rule_seqt,
                   cases i,
                   constructor,
                   apply sat_or_of_sat_split_right,
                   apply subset_append_left,
                   assumption,
                   apply sat_subset, swap, exact w.2,
                   rw erase_append_left _ i_h,
                   rw ←cons_append, simp
                 end
| (closed h₁) (closed h₂):= begin 
                              left,
                              clear or_rule_seqt,
                              cases i,
                              apply unsat_or_of_unsat_split_seqt, 
                              repeat {assumption}
                            end

def copy_rule_seqt {Γ Δ : seqt} (i : copy_instance_seqt Γ Δ) : node Δ → node Γ
| (closed h) := begin 
                  left,
                  clear copy_rule_seqt,
                  cases i with φ hmem,
                  apply unsat_copy_of_unsat_box,
                  repeat {assumption}
                end

| (open_ w)  := begin
                  right,
                  clear copy_rule_seqt,
                  cases i with φ h,
                  constructor,
                  apply sat_copy_of_sat_box, exact h, exact w.2
                end

open batch_sat_seqt

def dia_rule_seqt {p : seqt → Prop} (f : Π Γ, p Γ → node Γ): Π Γ : list seqt, (∀ i∈Γ, p i) → 
psum ({i // i ∈ Γ ∧ unsatisfiable (seqt.main i ++ seqt.hdld i)}) {x : list model // batch_sat_seqt x Γ}
| [] h := psum.inr ⟨[], bs_nil⟩
| (hd :: tl) h := 
match f hd (h hd (by simp)) with
| (node.closed pr) := psum.inl ⟨hd, by simp, pr⟩
| (node.open_ w₁) := 
  match dia_rule_seqt tl (λ x hx, h x $ by simp [hx]) with
  | (psum.inl uw) := begin 
                       left, rcases uw with ⟨w, hin, h⟩, 
                       split, split, swap, exact h, simp [hin]
                     end
  | (psum.inr w₂) := psum.inr ⟨(w₁.1::w₂), bs_cons _ _ _ _ w₁.2 w₂.2⟩
  end
end
