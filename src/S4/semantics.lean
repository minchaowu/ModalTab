import .ops
open subtype nnf tmodel list

section
variables (φ ψ : nnf) (Γ₁ Γ₂ Δ Λ: list nnf) {st : Type}
variables (k : S4 st) (s : st)
open list

theorem sat_subset (h₁ : Γ₁ ⊆ Γ₂) (h₂ : sat k s Γ₂) : sat k s Γ₁ :=
λ x hx, h₂ _ (h₁ hx)

theorem sat_sublist (h₁ : Γ₁ <+ Γ₂) (h₂ :sat k s Γ₂) : sat k s Γ₁ := 
sat_subset _ _ _ _ (sublist.subset h₁) h₂

theorem sat_append (h₁ : sat k s Γ₁) (h₂ : sat k s Γ₂) : sat k s (Γ₁ ++ Γ₂) :=
begin
  intros φ h, rw mem_append at h, cases h,
  apply h₁ _ h, apply h₂ _ h
end

theorem unsat_contra  {Δ n} : var n ∈ Δ →  neg n ∈ Δ →  unsatisfiable Δ:= 
begin
  intros h₁ h₂, intros v hsat, intros s hsat,
  have := hsat _ h₁, have := hsat _ h₂, simpa
end

theorem unsat_contra_seqt {Δ : sseqt} {n} : var n ∈ Δ.m →  neg n ∈ Δ.m →  unsatisfiable (Δ.m ++ Δ.b):= 
begin
  intros h₁ h₂, intros st m, intros s hsat,
  have := unsat_contra h₁ h₂,
  have := this _ m s,
  apply this,
  apply sat_subset _ _ _ _ _ hsat, 
  simp
end

theorem sat_of_and : force k s (and φ ψ) ↔ (force k s φ) ∧ (force k s ψ) := 
by split; {intro, simpa}

theorem sat_of_sat_erase (h₁ : sat k s $ Δ.erase φ) (h₂ : force k s φ) : sat k s Δ := 
begin
  intro ψ, intro h,
  by_cases (ψ = φ),
  {rw h, assumption},
  {have : ψ ∈ Δ.erase φ,
   rw mem_erase_of_ne, assumption, exact h,
   apply h₁, assumption}
end

theorem unsat_and_of_unsat_split 
        (h₁ : and φ ψ ∈ Δ) 
        (h₂ : unsatisfiable $ φ :: ψ :: Δ.erase (and φ ψ)) : 
        unsatisfiable Δ :=
begin
  intro st, intros, intro h,
  apply h₂, swap 3, exact k, swap, exact s,
  intro e, intro he,
  cases he,
  {rw he, have := h _ h₁, rw sat_of_and at this, exact this.1},
  {cases he, 
    {rw he, have := h _ h₁, rw sat_of_and at this, exact this.2}, 
    {have := h _ h₁, apply h, apply mem_of_mem_erase he} }
end

theorem unsat_and_of_unsat_split_seqt {Γ}
        (h₁ : and φ ψ ∈ Δ) 
        (h₂ : unsatisfiable $ (φ :: ψ :: Δ.erase (and φ ψ)++Γ)) : 
        unsatisfiable (Δ++Γ) :=
begin
  intro st, intros, intro h,
  apply h₂, swap 3, exact k, swap, exact s,
  intro e, intro he,
  cases he,
  {rw he, have := h _ (mem_append_left _ h₁), rw sat_of_and at this, exact this.1},
  {cases he, 
    {rw he, have := h _ (mem_append_left _ h₁), rw sat_of_and at this, exact this.2},
    {have := h _ (mem_append_left _ h₁), apply h, apply mem_of_mem_erase, rw erase_append_left, exact he, exact h₁} }
end

theorem sat_and_of_sat_split
        (h₁ : and φ ψ ∈ Δ) 
        (h₂ : sat k s $ φ :: ψ :: Δ.erase (and φ ψ)) : 
        sat k s Δ := 
begin
  intro e, intro he,
  by_cases (e = and φ ψ),
  { rw h, dsimp, split, repeat {apply h₂, simp} },
  { have : e ∈ Δ.erase (and φ ψ),
      { rw mem_erase_of_ne, repeat { assumption } },
    apply h₂, simp [this] }
end

theorem sat_and_of_sat_split_seqt {Γ}
        (h₁ : and φ ψ ∈ Δ) 
        (h₂ : sat k s $ (φ :: ψ :: Δ.erase (and φ ψ)++Γ)) : 
        sat k s (Δ++Γ) := 
begin
  intro e, intro he,
  by_cases (e = and φ ψ),
  { rw h, dsimp, split, repeat {apply h₂, simp} },
  { have : e ∈ Δ.erase (and φ ψ) ++ Γ,
      { rw ←erase_append_left, rw mem_erase_of_ne, repeat {assumption} },
    apply h₂, simp [this] }
end

theorem sat_split_of_sat_and_seqt {Γ}
        (h₁ : and φ ψ ∈ Δ) 
        (h₂ : sat k s (Δ++Γ)) : 
        sat k s $ (φ :: ψ :: Δ.erase (and φ ψ)++Γ) := 
begin
  intros e he, rw mem_append at he, cases he,
  have : force k s (and φ ψ), {apply h₂, simp [h₁]}, rw sat_of_and at this, 
  {cases he, 
  {rw he, exact this.left}, 
  {cases he, rw he, exact this.right, apply h₂, rw mem_append, left, apply mem_of_mem_erase he}
  },
  {apply h₂, rw mem_append, right, exact he}
end

theorem unsat_or_of_unsat_split_seqt {Γ}
        (h : or φ ψ ∈ Δ) 
        (h₁ : unsatisfiable $ (φ :: Δ.erase (nnf.or φ ψ)++Γ)) 
        (h₂ : unsatisfiable $ (ψ :: Δ.erase (nnf.or φ ψ)++Γ)) : 
        unsatisfiable $ (Δ++Γ) := 
begin
  intro, intros, intro hsat,
  have := hsat _ (mem_append_left _ h),
  dsimp at this,
  cases this,
  {apply h₁, swap 3, exact k, swap, exact s, intro e, intro he, 
   cases he, rw he, exact this, apply hsat, 
apply mem_of_mem_erase, rw erase_append_left, exact he, exact h},
  {apply h₂, swap 3, exact k, swap, exact s, intro e, intro he, 
   cases he, rw he, exact this, apply hsat, apply mem_of_mem_erase, rw erase_append_left, exact he, exact h}
end

theorem sat_or_of_sat_split_left 
        (h : or φ ψ ∈ Δ) 
        (hl : sat k s $ φ :: Δ.erase (nnf.or φ ψ)) :
        sat k s Δ := 
begin
  intros e he,
  by_cases (e = or φ ψ),
  { rw h, dsimp, left, apply hl, simp},
  {have : e ∈ Δ.erase (or φ ψ),
     { rw mem_erase_of_ne, repeat { assumption } },
   apply hl, simp [this]}
end

theorem sat_or_of_sat_split_right
        (h : or φ ψ ∈ Δ) 
        (hl : sat k s $ ψ :: Δ.erase (nnf.or φ ψ)) :
        sat k s Δ := 
begin
  intros e he,
  by_cases (e = or φ ψ),
  { rw h, dsimp, right, apply hl, simp},
  { have : e ∈ Δ.erase (or φ ψ),
      { rw mem_erase_of_ne, repeat { assumption } },
    apply hl, simp [this] }
end

/- S4-specific lemmas -/

theorem force_of_force_box (h : force k s $ box φ) : force k s φ 
:= by apply h; apply k.refl

theorem force_box_box_of_force_box : force k s (box φ) → force k s (box (box φ)) :=
by intros h s₁ rs₁ s₂ rs₂; apply h; apply k.trans rs₁ rs₂

theorem unsat_of_unsat_box_new
        (h₁ : box φ ∈ Δ) 
        (h₂ : unsatisfiable $ (φ :: Δ.erase (box φ)) ++ box φ :: Λ) : 
        unsatisfiable (Δ ++ Λ) :=
begin
  intros st k s h,
  apply h₂, swap 3, exact k, swap, exact s,
  intros e he,
  rw [mem_append] at he,
  cases he,
  {cases he, 
    {rw he, apply force_of_force_box, apply h (box φ), simp [h₁]},
    {apply h, rw mem_append, left, apply mem_of_mem_erase he }},
  {cases he, 
    {rw ←he at h₁, apply h, rw mem_append, left, exact h₁},
    {apply h, rw mem_append, right, assumption}}
end

theorem sat_copy_of_sat_box_new
        (h₁ : box φ ∈ Δ) 
        (h₂ : sat k s $ (φ :: Δ.erase (box φ)) ++ box φ :: Λ) : 
        sat k s (Δ ++ Λ) :=
begin
  intros ψ hφ,
  rw mem_append at hφ,
  cases hφ,
  {by_cases heq : ψ = box φ, 
    {rw heq, apply h₂ (box φ), simp}, 
    {have := mem_erase_of_ne heq, rw ←this at hφ, apply h₂, simp, right, left, exact hφ}},
  {apply h₂, simp, repeat {right}, exact hφ}
end

theorem unsat_of_unsat_box_dup
        (h₁ : box φ ∈ Δ)
        (h₃ : unsatisfiable $ (φ :: Δ.erase (box φ)) ++ Λ) : 
        unsatisfiable (Δ ++ Λ) :=
begin
  intros st k s h,
  apply h₃, swap 3, exact k, swap, exact s,
  intros e he,
  cases he,
  {rw he, apply force_of_force_box, apply h (box φ), simp [h₁]},
  {have := mem_append.1 he, cases this, 
   {apply h, apply mem_append_left, apply mem_of_mem_erase this},
   {apply h, apply mem_append_right, exact this}}
end

end

def unmodal_seqt (Γ : sseqt) : list sseqt :=
@list.pmap _ _ (λ φ, φ ∉ Γ.h ∧ dia φ ∈ Γ.m)
(λ d h,
({s := some {d := d, b := Γ.b},
a := {d := d, b := Γ.b} :: Γ.a,
h := d :: Γ.h,
m := d :: Γ.b,
ndh := begin rw list.nodup_cons, split, exact h.1, exact Γ.ndh end,
sph := begin apply list.cons_subperm_of_mem, apply Γ.ndh, exact h.1, apply mem_closure_dia, apply Γ.sbm, exact h.2,  exact Γ.sph end,
sbm := begin rw list.cons_subset, split, apply mem_closure_dia, apply Γ.sbm, exact h.2, apply list.subperm.subset, exact Γ.spb end,
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
sbm := begin rw list.cons_subset, split, apply mem_closure_dia, apply Γ.sbm, exact h.2, apply list.subperm.subset, exact Γ.spb end,
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
       sbm := begin rw list.cons_subset, split, apply mem_closure_dia, apply Γ.sbm, exact h.2, apply list.subperm.subset, exact Γ.spb end,
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
