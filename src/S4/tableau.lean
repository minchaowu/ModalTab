import .full_language .vanilla

def fml_is_sat (Γ : list fml) : bool :=
let l : list nnf := list.map fml.to_nnf Γ in
match tableau (mk_sseqt l) with
| node.closed _  := ff
| node.open_ _ := tt
end

theorem classical_correctness (Γ : list fml) : 
fml_is_sat Γ = tt ↔ ∃ (st : Type) (k : S4 st) s, fml_sat k s Γ := 
begin
  cases h : fml_is_sat Γ,
  constructor,
  { intro, contradiction },
  { intro hsat, cases eq : tableau (mk_sseqt (list.map fml.to_nnf Γ)), 
    rcases hsat with ⟨w, k, s, hsat⟩,
    apply false.elim, apply a, 
    rw trans_sat_iff at hsat, 
    swap 3, exact k, swap, exact s,
    dsimp [mk_sseqt], rw list.append_nil,
    exact hsat,
    { dsimp [fml_is_sat] at h,  dsimp [mk_sseqt] at eq, rw eq at h, contradiction } },
  { split, intro, dsimp [fml_is_sat] at h, 
     cases eq : tableau (mk_sseqt (list.map fml.to_nnf Γ)),
     { dsimp [mk_sseqt] at eq, rw eq at h, contradiction },
  { have he := model_existence a_1.1, 
    have h12:= a_1.2, 
    cases a_1.val with tm ptm,
    cases tm with itm ltm sgtm,
    simp at h12, dsimp [manc] at he,
    have hman : manc (tmodel.cons itm ltm sgtm) = [], {simp, rw h12},
    have hsub : itm.id.m ⊆ htk (tmodel.cons itm ltm sgtm), {simp, exact itm.mhtk},
    have := he hman _ hsub,
    rcases this with ⟨st, k, w, hw⟩,
    split, split, split,
    rw h12 at hw, simp at hw,
    rw ←trans_sat_iff at hw, 
    exact hw},
  { simp } }
end

open fml

def fml.exm : fml := or (var 1) (neg (var 1))

def K : fml := impl (box (impl (var 1) (var 2))) (impl (box $ var 1) (box $ var 2))
