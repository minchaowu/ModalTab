import .rules

open psum nnf node

set_option eqn_compiler.zeta true

def tableau : Π Γ : seqt, node Γ
| Γ := 
match get_contra_seqt Γ with 
| inl w := contra_rule_seqt w.2
| inr no_contra := 
  match get_and_seqt Γ with
  | inl p := 
  let Δ := p.1.1 :: p.1.2 :: Γ.main.erase (and p.val.1 p.val.2) in 
  let inst := and_instance_seqt.cons p.2 in
  have h : prod.measure_lex seqt_size ⟨_,_,_,_⟩ Γ, 
  begin apply split_lt_and_seqt, exact p.2 end,
  let d_delta : node ⟨Δ, Γ.hdld,_,_⟩ := tableau (and_child Γ p.2) in 
  and_rule_seqt inst d_delta
  | inr no_and := 
    match get_or_seqt Γ with
    | inl p := 
    let Γ₁ := p.1.1 :: Γ.main.erase (nnf.or p.val.1 p.val.2) in 
    let Γ₂ := p.1.2 :: Γ.main.erase (nnf.or p.val.1 p.val.2) in 
    let inst := or_instance_seqt.cons p.2 in
    have h₁ : prod.measure_lex seqt_size ⟨Γ₁, Γ.hdld,_,_⟩ Γ, 
    begin apply split_lt_or_seqt_left, exact p.2 end,
    have h₂ : prod.measure_lex seqt_size ⟨Γ₂, Γ.hdld,_,_⟩ Γ, 
    begin apply split_lt_or_seqt_right, exact p.2 end,
    let d_Γ₁ : node ⟨Γ₁, Γ.hdld,_,_⟩ := tableau (or_child_left Γ p.2) in 
    let d_Γ₂ : node ⟨Γ₂, Γ.hdld,_,_⟩ := tableau (or_child_right Γ p.2) in 
    or_rule_seqt inst d_Γ₁ d_Γ₂
    | inr no_or := 
      match get_box_seqt Γ with
      | inl p := 
      let Γ₁ := p.1 :: Γ.main.erase (nnf.box p.1) in
      let inst := copy_instance_seqt.cons p.2 in
      have h : prod.measure_lex seqt_size ⟨Γ₁, box p.1 :: Γ.hdld,_,_⟩ Γ, 
      begin apply copy_lt_seqt, exact p.2 end,
      let d_delta : node ⟨Γ₁, box p.1 :: Γ.hdld,_,_⟩ := tableau (box_child Γ p.2) in
      copy_rule_seqt inst d_delta
      | inr no_box := 
        match get_dia_seqt Γ with
        | inl p := 
        let ma : modal_applicable Γ := 
            {satu := {no_and := no_and, no_or := no_or},
             no_contra_main := no_contra, 
             no_box_main := no_box,
             v := get_var Γ.main,
             hv := λ n, get_var_iff,
             φ := p.1,
             ex := p.2} in 
        let l := @dia_rule_seqt (λ Δ, prod.measure_lex seqt_size Δ Γ) 
                 (λ x h, tableau x) (unmodal_seqt Γ) 
                 (unmodal_seqt_size Γ) in
        match l with
        | inl w := 
          begin left, {exact unsat_of_unsat_unmodal ma w.1 w.2} end
        | inr w := 
          begin right, split, apply sat_of_batch_sat, exact ma, exact w.2 end
        end
        | inr no_dia := 
        let mc : model_constructible Γ := 
          {satu := {no_and := no_and, no_or := no_or},
           no_box_main := no_box,
           no_contra_main := no_contra, 
           v := get_var Γ.main,
           hv := λ n, get_var_iff,
           no_dia := no_dia} in 
        begin right, split, apply build_model_seqt, exact mc end
        end
      end
    end
  end
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, prod.measure_lex_wf seqt_size⟩], dec_tac := `[assumption]}

def is_sat (Γ : seqt) : bool :=
match tableau Γ with
| closed _ := ff
| open_ _  := tt
end

def test : seqt := ⟨[box (var 1), (neg 1)], [], begin intros, exfalso, apply list.not_mem_nil, exact a_1 end, box_only_nil⟩

#eval is_sat test
