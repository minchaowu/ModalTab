import .rules
open psum nnf node

set_option eqn_compiler.zeta true

def tableau : Π Γ : list nnf, node Γ
| Γ := 
match get_contra Γ with
| inl w          := contra_rule w.2
| inr no_contra  := 

  match get_and Γ with
  | inl p := 
  let Δ := p.1.1 :: p.1.2 :: Γ.erase (nnf.and p.val.1 p.val.2) in 
  let inst := and_instance.cons p.2 in
  have node_size ((p.val).fst :: (p.val).snd :: list.erase Γ (and ((p.val).fst) ((p.val).snd))) < node_size Γ, 
    by apply split_lt_and; exact p.2,
  let d_delta : node Δ := tableau Δ in and_rule inst d_delta
  | inr no_and := 

    match get_or Γ with
    | inl p := 
    let Γ₁ := p.1.1 :: Γ.erase (nnf.or p.val.1 p.val.2) in 
    let Γ₂ := p.1.2 :: Γ.erase (nnf.or p.val.1 p.val.2) in 
    let inst := or_instance.cons p.2 in
    have node_size ((p.val).fst :: list.erase Γ (or ((p.val).fst) ((p.val).snd))) < node_size Γ, 
      by apply split_lt_or_left; exact p.2,
    have node_size ((p.val).snd :: list.erase Γ (or ((p.val).fst) ((p.val).snd))) < node_size Γ, 
      by apply split_lt_or_right; exact p.2,
    let d_Γ₁ : node (p.1.1 :: Γ.erase (or p.val.1 p.val.2)) := tableau Γ₁ in
    match d_Γ₁ with
    | closed m hsat pm := if hprcp : left_prcp inst ∈ m then 
                          or_rule inst (closed m hsat pm) (tableau Γ₂)
                          else jump_rule inst m hsat pm hprcp
    | open_ w := open_rule inst w.2
    end
    | inr no_or := 

      match get_dia Γ with
      | inl p := 
      let ma : modal_applicable Γ := 
          {no_contra := no_contra, 
           no_and := no_and,
           no_or := no_or,
           v := get_var Γ,
           hv := λ n, get_var_iff,
           φ := p.1,
           ex := p.2} in 
      let l := @tmap (λ Δ, node_size Δ < node_size Γ) 
               (λ x h, tableau x) (unmodal Γ) 
               (unmodal_size Γ) in
      match l with
      | inl w := begin 
                   left, 
                   {exact unsat_of_unsat_unmodal ma w.1 w.2},
                   swap, {exact dia (list.head w.1) :: rebox (unbox Γ)}, 
                   { exact modal_pmark ma w.1 w.2, }
                 end
      | inr w := begin 
                   right, split, 
                   apply sat_of_batch_sat, 
                   exact ma, exact w.2 
                 end
      end
      | inr no_dia := 
      let mc : model_constructible Γ := 
          {no_contra := no_contra, 
           no_and := no_and,
           no_or := no_or,
           v := get_var Γ,
           hv := λ n, get_var_iff,
           no_dia := no_dia} in 
      by right; split; apply build_model; exact mc

      end

    end

  end

end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf node_size⟩]}

def is_sat (Γ : list nnf) : bool :=
match tableau Γ with
| closed _ _  _:= ff
| open_ _  := tt
end

theorem correctness (Γ : list nnf) : is_sat Γ = tt ↔ ∃ (st : Type) (k : kripke st) s, sat k s Γ := 
begin
  cases h : is_sat Γ,
  constructor,
  {intro, contradiction},
  {intro hsat, cases eq : tableau Γ, 
   rcases hsat with ⟨w, k, s, hsat⟩,
   apply false.elim, apply a, exact hsat,
   {dsimp [is_sat] at h, rw eq at h, contradiction} },
  {split, intro, dsimp [is_sat] at h, 
    cases eq : tableau Γ,
    { rw eq at h, contradiction },
  { split, split, split, exact a_1.2},
  { simp } }
end

/- The negation of the defining formula of K is unsatisfiable -/

def φ : nnf := 
and (box $ or (neg 1) (var 2)) (and (box $ var 1) (dia $ neg 2))

#eval is_sat [φ]

def exm : nnf :=
-- or (var 1) (neg 1)
and (var 1) (neg 1)

-- #eval is_sat [exm]
