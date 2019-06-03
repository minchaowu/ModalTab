import .ops
open subtype nnf tmodel list

def unmodal_seqt (Γ : sseqt) : list sseqt :=
@list.pmap _ _ (λ φ, φ ∉ Γ.h ∧ dia φ ∈ Γ.m)
(λ d h,
({s := some {d := d, b := Γ.b},
a := {d := d, b := Γ.b} :: Γ.a,
h := d :: Γ.h,
m := d :: Γ.b,
ndh := begin rw list.nodup_cons, split, exact h.1, exact Γ.ndh end,
sph := begin apply list.cons_subperm_of_mem, apply Γ.ndh, exact h.1, apply mem_closure_dia, apply Γ.sbm, exact h.2,  exact Γ.sph end,
sbm := begin rw list.cons_subset, split, apply mem_closure_dia, apply Γ.sbm, exact h.2, apply list.subset_of_subperm, exact Γ.spb end,
ha  := begin intros φ h, cases h with l r, rw l, simp, right, apply Γ.ha, exact r end,
ps₁ := begin simp [dsig] end,
ps₂ := begin simp [bsig] end,
.. Γ} : sseqt))
(filter_undia Γ.h Γ.m)
(begin
intros φ hmem,split, 
{apply mem_filter_dia_right, exact hmem},
{apply mem_filter_dia_right_aux, exact hmem}
end)

def unmodal_seqt_size (Γ : sseqt) : ∀ (i : sseqt),  i ∈ unmodal_seqt Γ → (prod.measure_lex' sseqt_size i Γ) := 
list.pmapp _ _ 
begin 
intros φ h hmem,
right, left,
apply length_sub_lt_of_nodup_subperm,
{apply Γ.sph},
{apply mem_closure_dia, apply Γ.sbm, exact h.2},
{exact h.1},
{exact Γ.ndh}
end 
_

def sat_unmodal_of_sat {Γ : sseqt} : ∀ (i : sseqt),  i ∈ unmodal_seqt Γ → 
(∀ {st : Type} (k : S4 st) s, 
sat k s (Γ.m ++ Γ.b) → ∃ s', sat k s' (i.m ++ i.b)) :=
list.pmapp _ _
begin
intros φ hninh hmem st k s h,
have hd : force k s (dia φ), 
  { apply h, rw mem_append, left, exact hninh.2 }, 
have hb : ∀ φ ∈ Γ.b, force k s (box φ), 
  { intros γ hγ, 
    have := box_only_ex Γ.hb hγ, cases this with w hw,
    rw hw, apply force_box_box_of_force_box,
    have := h _ (mem_append_right _ hγ), rw hw at this, exact this},
rcases hd with ⟨w, hrw, hfw⟩,
split, swap, exact w,
intros ψ hψ, simp at hψ, cases hψ,
{rw hψ, exact hfw},
{apply hb, exact hψ, exact hrw}
end
_

def unsat_of_unsat_unmodal {Γ : sseqt} (i : sseqt) : i ∈ unmodal_seqt Γ ∧ unsatisfiable (i.m ++ i.b) → unsatisfiable (Γ.m ++ Γ.b) := 
begin
  intro hex, intros st k s h,
  have := sat_unmodal_of_sat i hex.1 k s h,
  cases this with w hw,
  have := hex.2,
  exact this _ _ _ hw
end

def unmodal_mem_box (Γ : sseqt) : ∀ (i : sseqt),  i ∈ unmodal_seqt Γ → (∀ φ, box φ ∈ Γ.b → box φ ∈ i.m) := 
list.pmapp _ _ begin intros φ h hmem ψ hψ, right, exact hψ end _

def mem_unmodal_seqt (Γ : sseqt) (φ) (h : φ ∉ Γ.h ∧ dia φ ∈ Γ.m) : ∃ (i : sseqt), i ∈ unmodal_seqt Γ ∧ φ ∈ i.m := 
begin
split, swap,
{exact 
({s := some {d := φ, b := Γ.b},
a := {d := φ, b := Γ.b} :: Γ.a,
h := φ :: Γ.h,
m := φ :: Γ.b,
ndh := begin rw list.nodup_cons, split, exact h.1, exact Γ.ndh end,
sph := begin apply list.cons_subperm_of_mem, apply Γ.ndh, exact h.1, apply mem_closure_dia, apply Γ.sbm, exact h.2,  exact Γ.sph end,
sbm := begin rw list.cons_subset, split, apply mem_closure_dia, apply Γ.sbm, exact h.2, apply list.subset_of_subperm, exact Γ.spb end,
ha  := begin intros φ h, cases h with l r, rw l, simp, right, apply Γ.ha, exact r end,
ps₁ := begin intro, simp [dsig] end,
ps₂ := begin intro, simp [bsig] end,
.. Γ} : sseqt)},
{ dsimp [unmodal_seqt], split,
  {let mf := (λ (d : nnf) (h : d ∉ Γ.h ∧ dia d ∈ Γ.m),
      ({s := some {d := d, b := Γ.b},
       a := {d := d, b := Γ.b} :: Γ.a,
       h := d :: Γ.h,
       m := d :: Γ.b,
       ndh := begin rw list.nodup_cons, split, exact h.1, exact Γ.ndh end,
       sph := begin apply list.cons_subperm_of_mem, apply Γ.ndh, exact h.1, apply mem_closure_dia, apply Γ.sbm, exact h.2,  exact Γ.sph end,
       sbm := begin rw list.cons_subset, split, apply mem_closure_dia, apply Γ.sbm, exact h.2, apply list.subset_of_subperm, exact Γ.spb end,
       ha  := begin intros φ h, cases h with l r, rw l, simp, right, apply Γ.ha, exact r end,
       ps₁ := begin simp [dsig] end,
       ps₂ := begin simp [bsig] end,
       .. Γ} :sseqt)),
  have hmem := mem_filter_undia_left _ _ _ h.2 h.1,
  have hf : ∀ (y : nnf), y ∈ filter_undia (Γ.h) (Γ.m) → y ∉ Γ.h ∧ dia y ∈ Γ.m, 
    {intros h hy, split, {apply mem_filter_dia_right, exact hy}, {apply mem_filter_dia_right_aux, exact hy}},
  exact mem_pmap_of_mem mf hmem hf},
{ simp } }
end

theorem unmodal_sig (Γ : sseqt) : ∀ (i : sseqt),  i ∈ unmodal_seqt Γ → (∀ a, a ∈ i.a → some a = i.s ∨ a ∈ Γ.a) := 
list.pmapp _ _ 
begin 
intros φ h hmem a ha, simp at ha,
cases ha,
{left, simp, exact ha},
{right, exact ha}
end 
_


theorem unsat_of_closed_and {Γ Δ} (i : and_instance Γ Δ) (h : unsatisfiable Δ) : unsatisfiable Γ := 
by cases i; { apply unsat_and_of_unsat_split, repeat {assumption} }

theorem unsat_of_closed_and_seqt {Γ Δ} (i : and_instance_seqt Γ Δ) (h : unsatisfiable (Δ.m++Δ.b)) : unsatisfiable (Γ.m++Γ.b) := 
by cases i; {apply unsat_and_of_unsat_split_seqt, repeat {assumption} }

theorem unsat_of_closed_or_seqt {Γ₁ Γ₂ Δ : sseqt} (i : or_instance_seqt Δ Γ₁ Γ₂) 
(h₁ : unsatisfiable (Γ₁.m++Γ₁.b)) 
(h₂ : unsatisfiable (Γ₂.m++Γ₂.b)) : 
unsatisfiable (Δ.m++Δ.b) :=
by cases i; {apply unsat_or_of_unsat_split_seqt, repeat { assumption }}

theorem unsat_of_closed_box_new {Γ Δ} (i : box_new_instance_seqt Γ Δ) (h : unsatisfiable $ (Δ.m++Δ.b)) : unsatisfiable (Γ.m++Γ.b) := 
by cases i; { apply unsat_of_unsat_box_new, repeat { assumption } }

theorem unsat_of_closed_box_dup {Γ Δ} (i : box_dup_instance_seqt Γ Δ) (h : unsatisfiable $ (Δ.m++Δ.b)) : unsatisfiable (Γ.m++Γ.b) := 
by cases i; { apply unsat_of_unsat_box_dup, repeat { assumption } }
