import defs
open nnf tactic

meta def frame_restriction : tactic unit :=
do intro `a >> `[simp]

structure KT (states : Type) extends kripke states :=
(refl : reflexive rel . frame_restriction)

instance inhabited_KT : inhabited (KT ℕ) := 
⟨{ val := λ a b, tt, rel := λ a b, tt }⟩

@[simp] def force {states : Type} (k : KT states) : states → nnf → Prop
| s (var n)    := k.val n s
| s (neg n)    := ¬ k.val n s
| s (and φ ψ)  := force s φ ∧ force s ψ
| s (or φ ψ)   := force s φ ∨ force s ψ
| s (box φ)    := ∀ s', k.rel s s' → force s' φ
| s (dia φ)    := ∃ s', k.rel s s' ∧ force s' φ

def sat {st} (k : KT st) (s) (Γ : list nnf) : Prop := 
∀ φ ∈ Γ, force k s φ

def unsatisfiable (Γ : list nnf) : Prop := 
∀ (st) (k : KT st) s, ¬ sat k s Γ

theorem unsat_singleton {φ} : unsatisfiable [φ] → ∀ (st) (k : KT st) s, ¬ force k s φ
 := 
begin
  intro h, intros, intro hf, 
  apply h, intros ψ hψ, rw list.mem_singleton at hψ, rw hψ, exact hf
end

theorem sat_of_empty {st} (k : KT st) (s) : sat k s [] :=
λ φ h, absurd h $ list.not_mem_nil _

theorem ne_empty_of_unsat {Γ} (h : unsatisfiable Γ): Γ ≠ [] := 
begin 
  intro heq, rw heq at h, 
  apply h, apply sat_of_empty, exact nat, 
  apply inhabited_KT.1, exact 0 
end

inductive model
| cons : list ℕ → list model → model

instance : decidable_eq model := by tactic.mk_dec_eq_instance

open model

@[simp] def mval : ℕ → model → bool
| p (cons v r) := if p ∈ v then tt else ff

@[simp] def mrel : model → model → bool
| m₁@(cons v r) m₂ := if m₂ ∈ r ∨ m₁ = m₂ then tt else ff 

theorem refl_mrel (s : model) : mrel s s := by cases s with v r; simp

theorem mem_of_mrel_tt : Π {v r m}, mrel (cons v r) m = tt → m ∈ r ∨ cons v r = m :=
begin
  intros v r m h, by_cases hc : cons v r = m,
  {right, exact hc},{left, by_contradiction hn, 
  have : mrel (cons v r) m = ff, { simp [hc, hn] },
  rw h at this, contradiction}
end

-- TODO : make this neater. Currently it's just a copy-paste
theorem mem_of_mrel_empty : Π {v m}, mrel (cons v []) m = tt → cons v [] = m :=
begin
  intros v m h, by_cases hc : cons v [] = m,
  {exact hc},
  {by_contradiction hn, 
  have : mrel (cons v []) m = ff, { simp [hc, hn] },
  rw h at this, contradiction}
end

@[simp] def builder : KT model := 
{val := λ n s, mval n s, rel := λ s₁ s₂, mrel s₁ s₂, refl := refl_mrel}

theorem force_box_of_leaf {v φ} (h : force builder (cons v []) φ): 
force builder (cons v []) (box φ) :=
begin
  dsimp, intros s' hs',
  have : cons v [] = s', {apply mem_of_mrel_empty, exact hs'},
  rw ←this, assumption
end

structure seqt : Type :=
(main : list nnf)
(hdld : list nnf) -- handled boxes
(pmain : ∀ {v l φ}, sat builder (cons v l) main → 
         box φ ∈ hdld → 
         (∀ ψ, box ψ ∈ hdld → ∀ m ∈ l, force builder m ψ) → 
         force builder (cons v l) φ) --TODO : make KT_model arbitrary
(phdld : box_only hdld)

class val_constructible (Γ : seqt) :=
(satu : saturated Γ.main)
(no_box_main : ∀ {φ}, box φ ∉ Γ.main)
(no_contra_main : ∀ {n}, var n ∈ Γ.main → neg n ∉ Γ.main)
(v : list ℕ)
(hv : ∀ n, var n ∈ Γ.main ↔ n ∈ v)

class modal_applicable (Γ : seqt) extends val_constructible Γ :=
(φ : nnf)
(ex : dia φ ∈ Γ.main)

class model_constructible (Γ : seqt) extends val_constructible Γ :=
(no_dia : ∀ {φ}, nnf.dia φ ∉ Γ.main)

theorem build_model : Π Γ (h : model_constructible Γ), 
sat builder (cons h.v []) Γ.main := 
begin
  intros, intro, intro hmem,
  cases heq : φ,
  case nnf.var : n {dsimp, have := h.hv, rw heq at hmem, rw this at hmem, simp [hmem]},
  case nnf.neg : n {dsimp, have h₁ := h.hv, rw heq at hmem, have := h.no_contra_main, simp, rw ←h₁, intro hvar, apply this, swap, exact hmem, exact hvar},
  case nnf.box : ψ {dsimp, intros, have := h.no_box_main, exfalso, rw heq at hmem, exact this hmem},
  case nnf.and : φ ψ { rw heq at hmem, have := h.satu.no_and, have := @this φ ψ, contradiction},
  case nnf.or : φ ψ { rw heq at hmem, have := h.satu.no_or, have := @this φ ψ, contradiction},
  case nnf.dia : φ { rw heq at hmem, have := h.no_dia, have := @this φ, contradiction},
end


/- Regular lemmas for the propositional part. -/

section
variables (φ ψ : nnf) (Γ₁ Γ₂ Δ Λ: list nnf) {st : Type}
variables (k : KT st) (s : st)
open list

theorem sat_subset (h₁ : Γ₁ ⊆ Γ₂) (h₂ : sat k s Γ₂) : sat k s Γ₁ :=
λ x hx, h₂ _ (h₁ hx)

theorem sat_sublist (h₁ : Γ₁ <+ Γ₂) (h₂ :sat k s Γ₂) : sat k s Γ₁ := 
sat_subset _ _ _ _ (subset_of_sublist h₁) h₂

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

theorem unsat_contra_seqt {Δ : seqt} {n} : var n ∈ Δ.main →  neg n ∈ Δ.main →  unsatisfiable (Δ.main ++ Δ.hdld):= 
begin
  intros h₁ h₂, intros st m, intros s hsat,
  have := unsat_contra h₁ h₂,
  have := this _ m s,
  apply this,
  apply sat_subset _ _ _ _ _ hsat, 
  simp
end

theorem sat_of_and : force k s (and φ ψ) ↔ (force k s φ) ∧ (force k s ψ) := 
by split; {intro, simpa}; {intro, simpa}

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

/- KT-specific lemmas -/

theorem force_of_force_box (h : force k s $ box φ) : force k s φ 
:= begin dsimp at h, apply h, apply k.refl end

theorem unsat_copy_of_unsat_box 
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

theorem sat_copy_of_sat_box 
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

theorem sat_box_of_sat_copy
        (h₁ : box φ ∈ Δ) 
        (h₂ : sat k s (Δ ++ Λ)) : 
        sat k s $ (φ :: Δ.erase (box φ)) ++ box φ :: Λ :=
begin
  apply sat_append,
  {intros ψ h, cases h, have : sat k s Δ, {apply sat_subset Δ (Δ++Λ), simp, assumption}, have := this _ h₁, apply force_of_force_box, rw h, exact this, apply h₂, have := mem_of_mem_erase h, simp [this]},
  {intros ψ h, cases h, rw h, have := h₂ (box φ), apply this, simp [h₁], apply h₂, rw mem_append, right, exact h}
end

end

def and_child {φ ψ} (Γ : seqt) (h : nnf.and φ ψ ∈ Γ.main) : seqt :=
⟨φ :: ψ :: Γ.main.erase (and φ ψ), Γ.hdld, 
begin 
  intros k s γ hsat hin hall, 
  by_cases heq : γ = and φ ψ,
  {rw heq, dsimp, split, apply hsat, simp, apply hsat, simp},
  {apply Γ.pmain, apply sat_and_of_sat_split, exact h, exact hsat, exact hin, exact hall}
end, 
Γ.phdld⟩

inductive and_instance_seqt (Γ : seqt) : seqt → Type
| cons : Π {φ ψ} (h : nnf.and φ ψ ∈ Γ.main), 
         and_instance_seqt $ and_child Γ h

def or_child_left {φ ψ} (Γ : seqt) (h : nnf.or φ ψ ∈ Γ.main) : seqt :=
⟨φ :: Γ.main.erase (or φ ψ), Γ.hdld, 
begin 
  intros k s γ hsat hin hall, 
  by_cases heq : γ = or φ ψ,
  {rw heq, dsimp, left, apply hsat, simp},
  {apply Γ.pmain, apply sat_or_of_sat_split_left, exact h, exact hsat, exact hin, exact hall}
end, 
Γ.phdld⟩

def or_child_right {φ ψ} (Γ : seqt) (h : nnf.or φ ψ ∈ Γ.main) : seqt :=
⟨ψ :: Γ.main.erase (or φ ψ), Γ.hdld, 
begin 
  intros k s γ hsat hin hall, 
  by_cases heq : γ = or φ ψ,
  {rw heq, dsimp, right, apply hsat, simp},
  {apply Γ.pmain, apply sat_or_of_sat_split_right, exact h, exact hsat, exact hin, exact hall}
end, 
Γ.phdld⟩

inductive or_instance_seqt (Γ : seqt) : seqt → seqt → Type
| cons : Π {φ ψ} (h : nnf.or φ ψ ∈ Γ.main),
         or_instance_seqt (or_child_left Γ h) (or_child_right Γ h)

def cons_box_only {φ Γ} (h : box_only Γ) : box_only (box φ :: Γ) := 
{no_var := begin intros n hn, cases hn, contradiction, apply h.no_var, exact hn end, 
no_neg := begin intros n hn, cases hn, contradiction, apply h.no_neg, exact hn end, 
no_and := begin intros ψ₁ ψ₂ hψ, cases hψ, contradiction, apply h.no_and, exact hψ end, 
no_or := begin intros ψ₁ ψ₂ hψ, cases hψ, contradiction, apply h.no_or, exact hψ end, 
no_dia := begin intros n hn, cases hn, contradiction, apply h.no_dia, exact hn end}

def box_child {φ} (Γ : seqt) (h : nnf.box φ ∈ Γ.main) : seqt :=
⟨φ :: Γ.main.erase (box φ), box φ :: Γ.hdld, 
begin 
  intros k s γ hsat hin hall, 
  cases hin,
  {simp at hin, rw hin, apply hsat, simp},
  {apply Γ.pmain, intros ψ hψ,
   by_cases heq : ψ = box φ,
   {rw heq, dsimp, intros s' hs', 
    have := mem_of_mrel_tt hs', cases this,
    {apply hall, simp, assumption},
    {rw ←this, apply hsat, simp} },
   {apply hsat, right, 
    have := list.mem_erase_of_ne heq, swap, exact Γ.main, 
    rw ←this at hψ, assumption},
  {assumption},{intros, apply hall, simp [a], exact H} }
end, 
cons_box_only Γ.phdld⟩

inductive copy_instance_seqt (Γ : seqt) : seqt → Type
| cons : Π {φ} (h : nnf.box φ ∈ Γ.main), 
         copy_instance_seqt $ box_child Γ h

theorem build_model_seqt : Π Γ (h : model_constructible Γ), 
sat builder (cons h.v []) (Γ.main ++ Γ.hdld) := 
begin 
  intros Γ h, apply sat_append, apply build_model,
  intros ψ hψ, 
  have := box_only_ex Γ.phdld hψ, cases this with w hw,
  rw hw, apply force_box_of_leaf, apply Γ.pmain _ _,
  {intros ψ hin m hm, exfalso, apply list.not_mem_nil, exact hm},
  {apply build_model},
  {rw hw at hψ, assumption}
end 
