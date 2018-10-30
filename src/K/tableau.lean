import .full_language .jump

def fml_is_sat (Γ : list fml) : bool :=
match tableau (list.map fml.to_nnf Γ) with
| node.closed _ _ _ := ff
| node.open_ _ := tt
end

theorem classical_correctness (Γ : list fml) : 
fml_is_sat Γ = tt ↔ ∃ (st : Type) (k : kripke st) s, fml_sat k s Γ := 
begin
  cases h : fml_is_sat Γ,
  constructor,
  { intro, contradiction },
  { intro hsat, cases eq : tableau (list.map fml.to_nnf Γ), 
    rcases hsat with ⟨w, k, s, hsat⟩,
    apply false.elim, apply a, rw trans_sat_iff at hsat, exact hsat,
    { dsimp [fml_is_sat] at h, rw eq at h, contradiction } },
  { split, intro, dsimp [fml_is_sat] at h, 
     cases eq : tableau (list.map fml.to_nnf Γ),
     { rw eq at h, contradiction },
  { split, split, split, have := a_1.2, rw ←trans_sat_iff at this, 
    exact this },
  { simp } }
end

#print axioms classical_correctness

open fml

def fml.exm : fml := or (var 1) (neg (var 1))

def K : fml := impl (box (impl (var 1) (var 2))) (impl (box $ var 1) (box $ var 2))

#eval fml_is_sat [neg fml.exm]

#eval fml_is_sat [neg K]
