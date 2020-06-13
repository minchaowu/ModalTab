import .semantics

inductive fml
| var (n : nat)         
| neg (φ : fml)         
| and (φ ψ : fml)       
| or (φ ψ : fml)        
| impl (φ ψ : fml)
| box (φ : fml)
| dia (φ : fml)

open fml

@[simp] def fml_size : fml → ℕ 
| (var n)    := 1
| (neg φ)    := fml_size φ + 1
| (and φ ψ)  := fml_size φ + fml_size ψ + 1
| (or φ ψ)   := fml_size φ + fml_size ψ + 1
| (impl φ ψ) := fml_size φ + fml_size ψ + 2
| (box φ)    := fml_size φ + 1
| (dia φ)    := fml_size φ + 1

@[simp] def fml_force {states : Type} (k : kripke states) : states → fml → Prop
| s (var n)    := k.val n s
| s (neg φ)    := ¬ fml_force s φ
| s (and φ ψ)  := fml_force s φ ∧ fml_force s ψ
| s (or φ ψ)   := fml_force s φ ∨ fml_force s ψ
| s (impl φ ψ) := ¬ fml_force s φ ∨ fml_force s ψ
| s (box φ)    := ∀ s', k.rel s s' → fml_force s' φ
| s (dia φ)    := ∃ s', k.rel s s' ∧ fml_force s' φ

@[simp] def fml.to_nnf : fml → nnf
| (var n)          := nnf.var n
| (neg (var n))    := nnf.neg n
| (neg (neg φ))    := fml.to_nnf φ
| (neg (and φ ψ))  := nnf.or (fml.to_nnf (neg φ)) (fml.to_nnf (neg ψ))
| (neg (or φ ψ))   := nnf.and (fml.to_nnf (neg φ)) (fml.to_nnf (neg ψ))
| (neg (impl φ ψ)) := nnf.and (fml.to_nnf φ) (fml.to_nnf (neg ψ))
| (neg (box φ))    := nnf.dia (fml.to_nnf (neg φ))
| (neg (dia φ))    := nnf.box (fml.to_nnf (neg φ))
| (and φ ψ)        := nnf.and (fml.to_nnf φ) (fml.to_nnf ψ)
| (or φ ψ)         := nnf.or (fml.to_nnf φ) (fml.to_nnf ψ)
| (impl φ ψ)       := nnf.or (fml.to_nnf (neg φ)) (fml.to_nnf ψ)
| (box φ)          := nnf.box (fml.to_nnf φ)
| (dia φ)          := nnf.dia (fml.to_nnf φ)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf fml_size⟩]}

@[simp] def trans_size_left {st} (k : kripke st) : (Σ' (s) (φ : fml), fml_force k s φ) → ℕ := 
λ h, fml_size h.snd.fst

@[simp] def trans_size_right {st} (k : kripke st) : (Σ' (s : st) (φ : fml), force k s (fml.to_nnf φ)) → ℕ := 
λ h, fml_size h.snd.fst

/- This direction requires choice -/

theorem trans_left {st} (k : kripke st) : Π s φ, 
fml_force k s φ → force k s (fml.to_nnf φ)
| s (var n)          h := h
| s (neg (var n))    h := h
| s (neg (neg φ))    h := by dsimp at h; rw classical.not_not at h; exact trans_left _ _ h
| s (neg (and φ ψ))  h := begin
                            have := trans_left s (neg φ),
                            dsimp at h,
                            rw classical.not_and_distrib at h,
                            cases h with l r,
                            {simp [trans_left _ (neg φ) l]},
                            {simp [trans_left _ (neg ψ) r]}
                          end
| s (neg (or φ ψ))   h := begin
                            dsimp at h,
                            rw not_or_distrib at h,
                            simp [and.intro (trans_left _ (neg φ) h.1) (trans_left _ (neg ψ) h.2)]
                          end
| s (neg (impl φ ψ)) h := begin
                            dsimp at h,
                            rw not_or_distrib at h,
                            have : force k s (fml.to_nnf φ), 
                              { apply trans_left, have := h.1, 
                                rw classical.not_not at this, 
                                exact this }, 
                            simp [and.intro this (trans_left _ (neg ψ) h.2)]
                          end
| s (neg (box φ))    h := begin
                            dsimp at h,
                            rw classical.not_forall at h,
                            cases h with w hw,
                            rw classical.not_imp at hw,
                            simp, split, split, 
                            {exact hw.1}, {apply trans_left, exact hw.2}
                          end
| s (neg (dia φ))    h := begin
                            dsimp at h, simp,
                            intros s' hs',
                            rw not_exists at h,
                            have := h s',
                            rw not_and at this,
                            have hnf := this hs',
                            apply trans_left, exact hnf
                          end
| s (and φ ψ)        h := by dsimp at h; simp [and.intro (trans_left _ _ h.1) (trans_left _ _ h.2)]
| s (or φ ψ)         h := begin
                            dsimp at h, cases h, 
                            {exact or.inl (trans_left _ _ h)}, 
                            {exact or.inr (trans_left _ _ h)}
                          end
| s (impl φ ψ)       h := begin
                            dsimp at h, simp,
                            cases h,
                            {left, apply trans_left, exact h}, 
                            {right, apply trans_left, exact h}
                          end
| s (box φ)          h := begin
                            dsimp at h, simp,
                            intros s' hs',
                            exact trans_left _ _ (h s' hs')
                          end
| s (dia φ)          h := begin
                            dsimp at h, simp,
                            cases h with w hw,
                            split, split, {exact hw.1}, {exact trans_left _ _ hw.2}
                          end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (trans_size_left k)⟩]}

/- This direction is still constructive -/

theorem trans_right {st} (k : kripke st) : Π s φ, 
force k s (fml.to_nnf φ) → fml_force k s φ
| s (var n)          h := h
| s (neg (var n))    h := h
| s (neg (neg φ))    h := by dsimp; simp at h; exact not_not_intro (trans_right _ _ h)
| s (neg (and φ ψ))  h := begin
                            dsimp, simp at h,
                            apply not_and_of_not_or_not,
                            cases h, 
                            {left, exact trans_right _ _ h}, 
                            {right, exact trans_right _ _ h}
                          end
| s (neg (or φ ψ))   h := begin
                            dsimp, simp at h,
                            apply not_or,
                            {exact trans_right _ _ h.1}, {exact trans_right _ _ h.2}
                          end
| s (neg (impl φ ψ)) h := begin
                            dsimp, simp at h,
                            apply not_or,
                            {exact not_not_intro (trans_right _ _ h.1)}, {exact trans_right _ _ h.2}
                          end
| s (neg (box φ))    h := begin
                            dsimp, simp at h,
                            apply not_forall_of_exists_not,
                            cases h with w hw,
                            split, 
                            {apply not_imp_of_and_not, split, exact hw.1, exact trans_right _ _ hw.2}
                          end
| s (neg (dia φ))    h := begin
                            dsimp, simp at h,
                            rw not_exists,
                            intros s' hs',
                            have := h s' hs'.1,
                            have hn := trans_right _ _ this,
                            have := hs'.2,
                            contradiction
                          end
| s (and φ ψ)        h := begin
                            dsimp, simp at h,
                            split, {exact trans_right _ _ h.1}, {exact trans_right _ _ h.2}
                          end
| s (or φ ψ)         h := begin
                            dsimp, simp at h,
                            cases h, {left, exact trans_right _ _ h}, {right, exact trans_right _ _ h}
                          end
| s (impl φ ψ)       h := begin
                            dsimp, simp at h, cases h,
                            {left, exact trans_right _ _ h}, {right, exact trans_right _ _ h}
                          end
| s (box φ)          h := begin
                            dsimp, simp at h,
                            intros s' hs',
                            exact trans_right _ _ (h s' hs')
                          end
| s (dia φ)          h := begin
                            dsimp, simp at h,
                            cases h with w hw,
                            split, split, {exact hw.1}, {exact trans_right _ _ hw.2}
                          end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (trans_size_right k)⟩]}

/- This is a classical result -/

theorem trans_iff {st} (k : kripke st) (s φ) : fml_force k s φ ↔ force k s (fml.to_nnf φ) := 
⟨trans_left k s φ, trans_right k s φ⟩

def fml_sat {st} (k : kripke st) (s) (Γ : list fml) : Prop := 
∀ φ ∈ Γ, fml_force k s φ

theorem fml_sat_of_empty {st} (k : kripke st) (s) : fml_sat k s [] :=
λ φ h, absurd h $ list.not_mem_nil _

def fml_unsatisfiable (Γ : list fml) : Prop := 
∀ (st) (k : kripke st) s, ¬ fml_sat k s Γ

theorem trans_sat_iff {st} (k : kripke st) (s) : Π Γ,
fml_sat k s Γ ↔ sat k s (list.map fml.to_nnf Γ)
| [] := by simp [sat_of_empty, fml_sat_of_empty]
| (hd::tl) := 
begin
split,
{ intro h, dsimp, intros φ hφ, cases hφ, 
  { rw hφ, rw ←trans_iff, apply h, simp },
  { have : fml_sat k s tl, 
      { intros ψ hψ, apply h, simp [hψ] }, 
    rw trans_sat_iff at this,
    exact this _ hφ } },
{ intros h φ hφ, cases hφ, 
  { rw hφ, rw trans_iff, apply h, simp }, 
  { have : sat k s (list.map fml.to_nnf tl), 
      { intros ψ hψ, apply h, simp [hψ] }, 
    rw ←trans_sat_iff at this,
    exact this _ hφ } }
end

theorem trans_unsat_iff (Γ : list fml) : fml_unsatisfiable Γ ↔ unsatisfiable (list.map fml.to_nnf Γ) := 
begin
  split, 
  {intros h _ _ _ _, apply h, rw trans_sat_iff, assumption}, 
  {intros h _ _ _ _, apply h, rw ←trans_sat_iff, assumption}
end

