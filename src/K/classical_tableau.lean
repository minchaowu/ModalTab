import .full_language .jump

def classical_is_sat (Γ : list fml) : bool :=
match tableau (list.map fml.to_nnf Γ) with
| node.closed _ _ _ := ff
| node.open_ _ := tt
end

theorem classical_correctness (Γ : list fml) : classical_is_sat Γ = tt ↔ ∃ (st : Type) (k : kripke st) s, fml_sat k s Γ := 
begin
  cases h : classical_is_sat Γ,
  constructor,
  { intro, contradiction },
  { intro hsat, cases eq : tableau (list.map fml.to_nnf Γ), 
    rcases hsat with ⟨w, k, s, hsat⟩,
    apply false.elim, apply a, rw trans_sat_iff at hsat, exact hsat,
    { dsimp [classical_is_sat] at h, rw eq at h, contradiction } },
  { split, intro, dsimp [classical_is_sat] at h, 
     cases eq : tableau (list.map fml.to_nnf Γ),
     { rw eq at h, contradiction },
  { split, split, split, have := a_1.2, rw ←trans_sat_iff at this, 
    exact this },
  { simp } }
end

def neg_exm : fml := fml.neg (fml.or (fml.var 1) (fml.neg (fml.var 1)))

#eval classical_is_sat [neg_exm]
