import .semantics data.list.perm

open nnf subtype list

def pmark (Γ m : list nnf) := ∀ Δ, (∀ δ ∈ Δ, δ ∉ m) → Δ <+ Γ → unsatisfiable (list.diff Γ Δ)

@[simp] def mark_and : nnf → list nnf → list nnf
| (nnf.and φ ψ) m := if φ ∈ m ∨ ψ ∈ m then nnf.and φ ψ :: m else
                     m
| _ m := m

@[simp] def mark_or : nnf → list nnf → list nnf → list nnf
| (nnf.or φ ψ) ml mr:= if φ ∈ ml ∨ ψ ∈ mr then nnf.or φ ψ :: (ml++mr) else ml ++ mr
| _ ml mr := ml ++ mr

theorem subset_mark_and {φ Γ} : Γ ⊆ mark_and φ Γ :=
begin
cases heq : φ,
case nnf.and : ψ₁ ψ₂ 
{ dsimp, 
  by_cases ψ₁ ∈ Γ ∨ ψ₂ ∈ Γ, 
  {rw if_pos h, simp},
  {rw if_neg h, simp} },
all_goals {simp}
end

theorem subset_mark_or_left {φ Γ₁ Γ₂} : Γ₁ ⊆ mark_or φ Γ₁ Γ₂:=
begin
cases heq : φ,
case nnf.or : ψ₁ ψ₂ 
{ dsimp, 
  by_cases ψ₁ ∈ Γ₁ ∨ ψ₂ ∈ Γ₂, 
  {rw if_pos h, rw ←cons_append, 
   apply subset_app_of_subset_left, simp},
  {rw if_neg h, simp} },
all_goals {simp}
end

theorem subset_mark_or_right {φ Γ₁ Γ₂} : Γ₂ ⊆ mark_or φ Γ₁ Γ₂:=
begin
cases heq : φ,
case nnf.or : ψ₁ ψ₂ 
{ dsimp, 
  by_cases ψ₁ ∈ Γ₁ ∨ ψ₂ ∈ Γ₂, 
  {rw if_pos h, rw ←cons_append, 
   apply subset_app_of_subset_right, simp},
  {rw if_neg h, simp} },
all_goals {simp}
end

def pmark_of_closed_and {Γ Δ} (i : and_instance Γ Δ) (m) (h : unsatisfiable Δ) (p : pmark Δ m) : {x // pmark Γ x} := 
begin
  cases i with φ ψ hin, split, swap,
  {exact mark_and (and φ ψ) m},
  { intros Δ' hΔ hsub,
    by_cases hm : φ ∈ m ∨ ψ ∈ m,
   -- pos hm
    { cases hm,
      -- left hm
      { have marked : nnf.and φ ψ ∈ mark_and (nnf.and φ ψ) m,
          {simp [mem_cons_self, hm] },
        have : unsatisfiable (list.diff (φ :: ψ :: list.erase Γ (and φ ψ)) Δ'),
          {apply p, 
           {intros δ hδ hmem, apply hΔ _ hδ, apply subset_mark_and hmem}, 
           have : Δ'.erase (and φ ψ) <+ φ :: ψ :: list.erase Γ (and φ ψ),
             {apply sublist.cons, apply sublist.cons, apply erase_sublist_erase _ hsub},
           have hnin: and φ ψ ∉ Δ',
             {intro, apply hΔ _ a marked},
           rw ←erase_of_not_mem hnin, exact this},
        intro, intros, intro hsat, 
        have hsat : sat k s (list.diff (φ :: ψ :: list.erase Γ (and φ ψ)) Δ'),
          {apply sat_subset _ (φ :: (ψ :: list.erase Γ (and φ ψ)).diff Δ'), 
           apply subset_cons_diff, apply sat_subset _ (φ :: ψ :: (list.erase Γ (and φ ψ)).diff Δ'), apply cons_subset_cons, apply subset_cons_diff,
           have hsatp : and φ ψ ∈ Γ.diff Δ',
             {apply mem_diff_of_mem hin, intro, apply hΔ _ a marked},
           intros x hx, rcases hx with eq₁ | eq₂ | hin',
           rw eq₁, apply and.left, rw ←sat_of_and, apply hsat _ hsatp, 
           rw eq₂, apply and.right, rw ←sat_of_and, apply hsat _ hsatp, 
           have hsubd : list.diff (list.erase Γ (and φ ψ)) Δ' ⊆ list.diff Γ Δ',
             {apply subset_of_sublist, apply diff_sublist_of_sublist, apply erase_sublist},
           apply hsat, apply hsubd, exact hin'},
        apply this, exact hsat }, 
      -- right hm
      { have marked : nnf.and φ ψ ∈ mark_and (nnf.and φ ψ) m,
         { simp [mem_cons_self, hm] },
        have : unsatisfiable (list.diff (φ :: ψ :: list.erase Γ (and φ ψ)) Δ'),
          {apply p, 
           {intros δ hδ hmem, apply hΔ _ hδ, apply subset_mark_and hmem}, 
          have : Δ'.erase (and φ ψ) <+ φ :: ψ :: list.erase Γ (and φ ψ),
            {apply sublist.cons, apply sublist.cons, apply erase_sublist_erase, exact hsub},
          have hnin: and φ ψ ∉ Δ',
            {intro, apply hΔ _ a marked},
          rw ←erase_of_not_mem hnin, exact this},
        intro, intros, intro hsat,
        have hsat : sat k s (list.diff (φ :: ψ :: list.erase Γ (and φ ψ)) Δ'),
          {apply sat_subset _ (φ :: (ψ :: list.erase Γ (and φ ψ)).diff Δ'), 
           apply subset_cons_diff, apply sat_subset _ (φ :: ψ :: (list.erase Γ (and φ ψ)).diff Δ'), apply cons_subset_cons, apply subset_cons_diff,
           have hsatp : and φ ψ ∈ Γ.diff Δ',
             {apply mem_diff_of_mem hin, intro, apply hΔ _ a marked},
           intros x hx, rcases hx with eq₁ | eq₂ | hin',
           rw eq₁, apply and.left, rw ←sat_of_and, apply hsat _ hsatp, 
           rw eq₂, apply and.right, rw ←sat_of_and, apply hsat _ hsatp, 
           have hsubd : list.diff (list.erase Γ (and φ ψ)) Δ' ⊆ list.diff Γ Δ',
             {apply subset_of_sublist, apply diff_sublist_of_sublist, apply erase_sublist},
           apply hsat, apply hsubd, exact hin'},
        apply this, exact hsat } },
  -- neg hm
   { have : unsatisfiable ((φ :: ψ :: list.erase Γ (and φ ψ)).diff $ φ :: ψ :: Δ'.erase (and φ ψ)),
       {apply p, intros δ hδ hdin, rcases hδ with eq₁ | eq₂ | hmem, 
         {apply hm, left, rw ←eq₁, exact hdin},
         {apply hm, right, rw ←eq₂, exact hdin},
         {apply hΔ, apply erase_subset _ _ hmem, apply subset_mark_and hdin},
        apply sublist.cons2, apply sublist.cons2, apply erase_sublist_erase _ hsub },
     intro, intros, intro hsat, apply this, simp, 
     apply sat_sublist, apply erase_diff_erase_sublist_of_sublist hsub, exact hsat } }
end

theorem unsat_of_jump {Γ₁ Γ₂ Δ : list nnf} (i : or_instance Δ Γ₁ Γ₂) 
(m : list nnf) (h₁ : unsatisfiable Γ₁) (h₂ : pmark Γ₁ m) 
(h₃ : left_prcp i ∉ m) : unsatisfiable Δ := 
begin
  cases i with φ ψ hin,
  have : unsatisfiable ((φ :: list.erase Δ (or φ ψ)).diff [φ]),
    {apply h₂, intros, cases H, rw H, exact h₃, intro, exact not_mem_nil δ H, apply sublist.cons2, simp},
  intro, intros, intro hsat, apply this,
  apply sat_subset _ Δ _ _ _ hsat, simp [erase_subset]
end
 
def pmark_of_jump {Γ₁ Γ₂ Δ : list nnf} (i : or_instance Δ Γ₁ Γ₂) 
(m : list nnf) (h₁ : unsatisfiable Γ₁) (h₂ : pmark Γ₁ m) 
(h₃ : left_prcp i ∉ m) : {x // pmark Δ x} := 
begin
  cases i with φ ψ hin,
  split, swap, {exact mark_or (or φ ψ) m []},
  { intros Δ' hΔ' hsub,
    have : unsatisfiable (list.diff (φ :: Δ.erase (or φ ψ)) (φ :: Δ'.erase (or φ ψ))),
      { apply h₂, intros, intro hmem, rcases H with eq | hin,
        {apply h₃, simpa [eq] using hmem},
        {apply hΔ' δ, apply erase_subset _ _ hin, apply subset_mark_or_left hmem},
      apply sublist.cons2, apply erase_sublist_erase _ hsub },
    intro, intros, intro hsat,
    apply this st k s, simp, apply sat_sublist, apply erase_diff_erase_sublist_of_sublist, exact hsub, exact hsat }
end

def pmark_of_closed_or {Γ₁ Γ₂ Δ : list nnf} {m₁ m₂ : list nnf} (i : or_instance Δ Γ₁ Γ₂) (h₁ : unsatisfiable Γ₁) (p₁ : pmark Γ₁ m₁) 
(h₂ : unsatisfiable Γ₂) (p₂ : pmark Γ₂ m₂) : {x // pmark Δ x} :=
begin
  cases i with φ ψ hin, split, swap,
  {exact mark_or (or φ ψ) m₁ m₂},
  {intros Δ' hΔ hsub,
    by_cases hmφ : φ ∈ m₁,
    { have marked : or φ ψ ∈ mark_or (or φ ψ) m₁ m₂,
        {simp [hmφ]},
      have hnin: or φ ψ ∉ Δ',
        {intro, apply hΔ _ a marked},
      have hl : unsatisfiable (list.diff (φ :: list.erase Δ (or φ ψ)) Δ'),
        {apply p₁, 
        {intros δ hδ hin, apply hΔ, exact hδ, apply subset_mark_or_left, exact hin}, 
        have : Δ'.erase (or φ ψ) <+ φ :: list.erase Δ (or φ ψ),
          {apply sublist.cons, apply erase_sublist_erase, exact hsub},
        rw ←erase_of_not_mem hnin, exact this},
      have hr : unsatisfiable (list.diff (ψ :: list.erase Δ (or φ ψ)) Δ'),
        {apply p₂, 
        {intros δ hδ hin, apply hΔ, exact hδ, apply subset_mark_or_right, exact hin}, 
        have : Δ'.erase (or φ ψ) <+ ψ :: list.erase Δ (or φ ψ),
          {apply sublist.cons, apply erase_sublist_erase, exact hsub},
        rw ←erase_of_not_mem hnin, exact this},
      intro, intros, intro hsat,
      have : or φ ψ ∈ list.diff Δ Δ',
        {apply mem_diff_of_mem hin hnin},
      have hforce := hsat _ this, dsimp at hforce,
      cases hforce with l r,
      { apply hl st k s, 
        apply sat_subset, 
        apply subset_of_subperm, 
        apply subperm_cons_diff, 
        intros x hx, 
        cases hx, rw hx, exact l, apply hsat,
        have hsubd : list.diff (list.erase Δ (or φ ψ)) Δ' ⊆ list.diff Δ Δ',
          {apply subset_of_sublist, apply diff_sublist_of_sublist, apply erase_sublist},
        apply hsubd hx },
      { apply hr st k s, 
        apply sat_subset, 
        apply subset_of_subperm, 
        apply subperm_cons_diff, 
        intros x hx, 
        cases hx, rw hx, exact r, apply hsat,
        have hsubd : list.diff (list.erase Δ (or φ ψ)) Δ' ⊆ list.diff Δ Δ',
          {apply subset_of_sublist, apply diff_sublist_of_sublist, apply erase_sublist},
        apply hsubd hx } },
{by_cases hmψ : ψ ∈ m₂, 
 -- marked ψ
 { have marked : or φ ψ ∈ mark_or (or φ ψ) m₁ m₂,
     {simp [hmψ]},
   have hnin: or φ ψ ∉ Δ',
     {intro, apply hΔ _ a marked},
   have hl : unsatisfiable (list.diff (φ :: list.erase Δ (or φ ψ)) Δ'),
     {apply p₁, 
     {intros δ hδ hin, apply hΔ, exact hδ, apply subset_mark_or_left, exact hin}, 
     have : Δ'.erase (or φ ψ) <+ φ :: list.erase Δ (or φ ψ),
       {apply sublist.cons, apply erase_sublist_erase, exact hsub},
     rw ←erase_of_not_mem hnin, exact this},
   have hr : unsatisfiable (list.diff (ψ :: list.erase Δ (or φ ψ)) Δ'),
     {apply p₂, 
     {intros δ hδ hin, apply hΔ, exact hδ, apply subset_mark_or_right, exact hin}, 
     have : Δ'.erase (or φ ψ) <+ ψ :: list.erase Δ (or φ ψ),
       {apply sublist.cons, apply erase_sublist_erase, exact hsub},
     rw ←erase_of_not_mem hnin, exact this},
   intro, intros, intro hsat,
   have : or φ ψ ∈ list.diff Δ Δ',
     {apply mem_diff_of_mem hin hnin},
   have hforce := hsat _ this, dsimp at hforce,
   cases hforce with l r,
   { apply hl st k s, 
     apply sat_subset, 
     apply subset_of_subperm, 
     apply subperm_cons_diff, 
     intros x hx, 
     cases hx, rw hx, exact l, apply hsat,
     have hsubd : list.diff (list.erase Δ (or φ ψ)) Δ' ⊆ list.diff Δ Δ',
       {apply subset_of_sublist, apply diff_sublist_of_sublist, apply erase_sublist},
     apply hsubd hx },
   { apply hr st k s, 
     apply sat_subset, 
     apply subset_of_subperm, 
     apply subperm_cons_diff, 
     intros x hx, 
     cases hx, rw hx, exact r, apply hsat,
     have hsubd : list.diff (list.erase Δ (or φ ψ)) Δ' ⊆ list.diff Δ Δ',
       {apply subset_of_sublist, apply diff_sublist_of_sublist, apply erase_sublist},
     apply hsubd hx } },
-- both unmarked
 { have : unsatisfiable (list.diff (φ :: Δ.erase (or φ ψ)) (φ :: Δ'.erase (or φ ψ))),
     {apply p₁, intros, intro hmem, rcases H with eq | hin,
      {apply hmφ, rw ←eq, exact hmem},
      {apply hΔ δ, apply erase_subset _ _ hin, apply subset_mark_or_left, exact hmem},
      apply sublist.cons2, apply erase_sublist_erase _ hsub},
   intro, intros, intro hsat, 
   apply this st k s, simp, apply sat_sublist, 
   apply erase_diff_erase_sublist_of_sublist hsub, exact hsat } } }
end

theorem modal_pmark {Γ} (h₁ : modal_applicable Γ) (i)
(h₂ : i ∈ unmodal Γ ∧ unsatisfiable i): 
pmark Γ (dia (list.head i) :: rebox (unbox Γ)) := 
begin
  intro, intros hδ hsub, intro, intros, intro hsat,
  have := unmodal_unsat_of_unsat Γ i h₂.1 h₂.2,
  apply this st k s,
  apply sat_subset _ _ _ _ _ hsat,
  intros φ h, apply mem_diff_of_mem,
  {cases h, rw h, exact unmodal_mem_head Γ i h₂.1,
   apply rebox_unbox_of_mem, {simp [unbox_iff]}, {exact h}},
  {intro, apply hδ, repeat {assumption} }
end
