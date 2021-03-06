import .rules

open psum nnf node

set_option eqn_compiler.zeta true

def tableau : Π Γ : sseqt, node Γ
| Γ := 
  match get_contra_seqt Γ with 
  | inl w := contra_rule_seqt w.2
  | inr no_contra :=
    match get_and_seqt Γ with
    | inl w := 
    let inst := and_instance_seqt.cons w.2 in
    have h : prod.measure_lex' sseqt_size (and_child Γ w.2) Γ,
    begin apply split_lt_and_seqt end,
    let d_delta := tableau (and_child Γ w.2) in
    and_rule_seqt inst d_delta
    | inr no_and := 
      match get_or_seqt Γ with
      | inl w := 
      let inst := or_instance_seqt.cons w.2 in 
      have h₁ : prod.measure_lex' sseqt_size (or_child_left Γ w.2) Γ,
      begin apply split_lt_or_seqt_left end,
      have h₂ : prod.measure_lex' sseqt_size (or_child_right Γ w.2) Γ,
      begin apply split_lt_or_seqt_right end,
      let Γ₁ := tableau (or_child_left Γ w.2) in
      match Γ₁ with
      | closed p := or_rule_seqt inst (closed p) (tableau (or_child_right Γ w.2))
      | open_ w := open_rule_seqt inst w.2
      end
      | inr no_or := 
        match get_box_seqt Γ with
        | inl w := -- term mode here helps termination 
        if hb : box w.1 ∈ Γ.b then
        let inst := box_dup_instance_seqt.cons w.2 hb in 
        have h : prod.measure_lex' sseqt_size (box_child Γ w.2) Γ,
        from copy_lt_seqt _ _,
        let d_delta := tableau (box_child Γ w.2) in
        box_rule_seqt inst d_delta
        else 
        let inst := box_new_instance_seqt.cons w.2 hb in 
        have h : prod.measure_lex' sseqt_size (box_child_new Γ w.2 hb) Γ,
        from box_new_lt_seqt _ _ _,
        let d_delta := tableau (box_child_new Γ w.2 hb) in
        box_new_rule_seqt inst d_delta
        | inr no_box := 
          match get_dia_seqt Γ with
          | inl w := 
          let ma : modal_applicable Γ := 
              {satu := {no_and := no_and, no_or := no_or},
               no_contra_main := no_contra, 
               no_box_main := no_box,
               φ := w.1,
               ex := w.2} in 
          let l := @dia_rule_seqt (λ Δ, prod.measure_lex' sseqt_size Δ Γ) 
                   (λ x h, tableau x) (unmodal_seqt Γ) 
                   (unmodal_seqt_size Γ) in
            match l with
            | inl w := begin left, exact unsat_of_unsat_unmodal w.1 w.2 end
            | inr w := 
            begin 
            right, split, swap,
            {let lm := models_to_tmodels w.1,
             let sgm := dia_rule_loop Γ.h Γ.b Γ.m,
             let mΓ : sseqt := Γ,
             let mhtk := Γ.m,
             have mhhtk : hintikka Γ.m, {apply hintikka_ma ma},
             have mmhtk : Γ.m ⊆ Γ.m, {simp},
             split, swap,
             {let minfo : info := ⟨mΓ, mhtk, mhhtk, mmhtk⟩,
              exact tmodel.cons minfo lm sgm },
             {split,
              {split,
               {simp, intros s hs, have := list.mem_map.1 hs, 
                rcases this with ⟨i, hmem, hi⟩, intros φ hφ, rw ←hi,
                apply mem_be_box, exact w.2, exact hmem, exact hφ},
               {simp, intros s hs φ hφ, exfalso, apply no_box, exact hφ},
               {simp, intros φ hφ, 
                by_cases hc : φ ∈ Γ.h,
                {left, have := mem_loop_left _ Γ.b _  _ hc hφ, split, split, exact this, simp},
                {right, have := mem_be_dia _ _ w.2 _ hφ hc, 
                 rcases this with ⟨i, hmem, hi⟩,
                 have := list.mem_map_of_mem (λ x : model, x.val) hmem,
                 split, split, exact this, exact hi} },
               {simp, intros s rq hdesc hmem, 
                have := ex_desc' _ _ lm _ hdesc,
                cases this with hl hr,
                {have hc := list.mem_map.1 hl,
                 rcases hc with ⟨ms, pmsl, pmsr⟩, 
                 have hci := be_ex _ _ w.2 _ pmsl,
                 rcases hci with ⟨iw, imem, pi⟩,
                 have ps := pt_of_m_to_tm _ _ hl,
                 have hsub := ps.1.sreq,
                 cases s with is ls sgs,
                 simp at hmem, simp at hsub,
                 have hin := hsub hmem,
                 rw pmsr at pi, simp at pi, rw pi at hin,
                 have := unmodal_sig _ _ imem _ hin,
                 cases this,
                 {right, split, swap, exact tmodel.cons is ls sgs, split, exact hdesc, simp, rw this, rw pi},
                 {left, exact this}},
                {rcases hr with ⟨c, memc, pdc⟩, 
                 have pc := pt_of_m_to_tm _ _ memc,
                 have := pc.1.bdia, 
                 cases c with ic lc sgc, simp at this,
                 have hc := this _ _ pdc hmem,
                 cases hc with hl hr,
                 {have hcc := list.mem_map.1 memc,
                  rcases hcc with ⟨ms, pmsl, pmsr⟩, 
                  have hci := be_ex _ _ w.2 _ pmsl,
                  rcases hci with ⟨iw, imem, pi⟩,
                  have ps := pt_of_m_to_tm _ _ memc,
                  rw pmsr at pi, simp at pi, rw pi at hl,
                  have hccc := unmodal_sig _ _ imem _ hl,
                  cases hccc,
                  {right, split, swap, exact tmodel.cons ic lc sgc, split, apply tc'.base, simp, exact memc, simp, rw hccc, rw pi},
                  {left, exact hccc} },
                 {right, 
                  rcases hr with ⟨d, ddesc, hd⟩,
                  split, swap, exact d, split,
                  {apply desc_ex, split, split, exact memc, exact ddesc},
                  {exact hd}}}},
               {simp, intros rq hrq φ hφ, cases hφ, 
                {exfalso, apply ma.no_box_main, exact hφ}, 
                {have := mem_loop_box _ _ _ _ hrq, rw this, exact hφ}},
               {simp, intros s hs, have := mem_loop_dia _ _ _ _ hs, 
                rcases this with ⟨w, hmem, hw⟩,
                have := Γ.ha _ hmem,
                have sb := mem_loop_box _ _ _ _ hs,
                cases s, rw ←hw at this, rw ←sb at this, simp at this, exact this}},
              {intros d hd, have := ex_desc' _ _ _ _ hd, 
               cases this, 
               {have pd := pt_of_m_to_tm _ _ this, exact pd.1}, 
               {rcases this with ⟨m, memm, mdesc⟩, 
                have pd := pt_of_m_to_tm _ _ memm,
                apply pd.2, exact mdesc}}}},
            {simp}
            end
          end
          | inr no_dia := 
          let mc : model_constructible Γ := 
            {satu := {no_and := no_and, no_or := no_or},
             no_box_main := no_box,
             no_contra_main := no_contra, 
             no_dia := no_dia} in build_model mc
          end 
        end
      end
    end
  end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, prod.measure_lex_wf' sseqt_size⟩], dec_tac := `[assumption]}

@[simp] def mk_sseqt (Γ : list nnf) : sseqt :=
{ goal := Γ,
  s := none,
  a := [],
  h := [],
  b := [],
  m := Γ,
  ndh := list.nodup_nil,
  ndb := list.nodup_nil,
  sph := list.nil_subperm,
  spb := list.nil_subperm,
  sbm := mem_closure_self _,
  ha := λ x hx, absurd hx $ list.not_mem_nil _,
  hb := box_only_nil,
  ps₁ := λ h, by contradiction,
  ps₂ := λ h, by contradiction }

def is_sat (Γ : list nnf) : bool :=
match tableau (mk_sseqt Γ) with
| closed _ := ff
| open_ _ := tt
end

theorem model_existence (m : model) (hrt : manc m.1 = []) 
(Γ : list nnf) (h : Γ ⊆ htk m.1) : ∃ (st : Type) (k : S4 st) s, sat k s Γ := 
begin
split, swap,
exact {x : rmodel // x.1 = m.1 ∨ desc x.1 m.1},
split, swap,
exact builder m.1,
split, swap,
split,
left, swap, exact ⟨m.1, m.2.1⟩,
simp,
intros φ hφ, apply good_model,
exact hrt, apply h, exact hφ
end

theorem correctness (Γ : list nnf) : is_sat Γ = tt ↔ ∃ (st : Type) (k : S4 st) s, sat k s Γ := 
begin
  cases h : is_sat Γ,
  constructor,
  {intro, contradiction},
  {intro hsat, cases eq : tableau (mk_sseqt Γ), 
   rcases hsat with ⟨w, k, s, hsat⟩,
   apply false.elim, apply a, simp, exact hsat,
   {dsimp [is_sat] at h, dsimp at eq, rw eq at h, contradiction}},
  {split, intro, dsimp [is_sat] at h, 
   cases eq : tableau (mk_sseqt Γ),
   {dsimp at eq, rw eq at h, contradiction},
   {apply model_existence, swap 3, exact a_1.1,
    have := a_1.2, simp at this,
    cases a_1.val with tm ptm,
    cases tm with itm ltm sgtm,
    simp, simp at this, rw this,
    have := a_1.2, simp at this, 
    cases a_1.val with tm ptm,
    cases tm with itm ltm sgtm,
    have hsub := itm.mhtk, simp, simp at this,
    rw this at hsub, dsimp at hsub, exact hsub},
  {simp}}
end

-- negation of K
def φ : nnf := 
and (box $ or (neg 1) (var 2)) (and (box $ var 1) (dia $ neg 2))

#eval is_sat [φ] -- ff

-- negation of S4
def ψ : nnf := and (box (var 1)) (dia (dia (neg 1)))

#eval is_sat [ψ] -- ff

def γ : nnf := and (and (dia (var 1)) (dia (var 2))) (box (or (neg 1) (neg 2)))

#eval is_sat [γ] -- tt
