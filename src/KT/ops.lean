import .size
open nnf list

namespace list
universes u v w

variables {α : Type u} {β : Type v} {γ : Type w}

theorem mapp {p : β → Prop} (f : α → β) : Π (l : list α) (h : ∀ x∈l, p (f x)) x, x ∈ list.map f l → p x
| [] h x := by simp
| (hd::tl) h x := 
begin
intro hmem, cases hmem,
{rw hmem, apply h, simp},
{apply mapp tl, intros a ha, apply h, simp [ha], exact hmem}
end

@[simp] def ne_empty_head : Π l : list α, l ≠ [] → α
| []       h := by contradiction
| (a :: l) h := a

end list

@[simp] def unbox : list nnf → list nnf
| [] := []
| ((box φ) :: l) := φ :: unbox l
| (e :: l) := unbox l

theorem unbox_iff : Π {Γ φ}, box φ ∈ Γ ↔ φ ∈ unbox Γ
| [] φ := begin split, repeat {intro h, simpa using h} end
| (hd::tl) φ := 
begin
  split,
  { intro h, cases h₁ : hd, 
    case nnf.box : ψ 
    { dsimp [unbox], cases h, 
       {left, rw h₁ at h, injection h},
       {right, exact (@unbox_iff tl φ).1 h} },
    all_goals 
    { dsimp [unbox], cases h, 
       {rw h₁ at h, contradiction},
       {exact (@unbox_iff tl φ).1 h} } },
  { intro h, cases h₁ : hd, 
    case nnf.box : ψ
    { rw h₁ at h, dsimp [unbox] at h, cases h, 
       {simp [h]}, {right, exact (@unbox_iff tl φ).2 h} },
    all_goals 
    { rw h₁ at h, dsimp [unbox] at h, right, exact (@unbox_iff tl φ).2 h } }
end

theorem unbox_size_aux : Π {Γ}, node_size (unbox Γ) ≤ node_size Γ
| [] := by simp
| (hd::tl) := 
begin
  cases h : hd,
  case nnf.box : ψ
  { dsimp, apply add_le_add, 
     { dsimp [sizeof, has_sizeof.sizeof, nnf.sizeof], 
       rw add_comm, apply nat.le_succ }, 
     { apply unbox_size_aux } },
  all_goals 
  { dsimp, apply le_add_of_nonneg_of_le, 
    { dsimp [sizeof, has_sizeof.sizeof, nnf.sizeof], rw add_comm, apply nat.zero_le }, 
    { apply unbox_size_aux } }
end

theorem le_of_unbox_degree : Π {Γ}, modal_degree (unbox Γ) ≤ modal_degree Γ
| [] := by simp
| (hd::tl) := 
begin
cases heq : hd,
case nnf.box : ψ 
{dsimp, rw cons_degree, rw cons_degree, 
apply max_le_of_le, { simp }, { apply le_of_unbox_degree } },
all_goals
{dsimp, rw cons_degree, apply le_max_of_le_right, apply le_of_unbox_degree}
end

theorem zero_degree_of_eq_unbox : Π {Γ}, modal_degree (unbox Γ) = modal_degree Γ → modal_degree Γ = 0 
| [] h := begin dsimp [maximum, modal_degree], reflexivity end
| (hd::tl) h := 
begin
cases heq : hd,
case nnf.box : ψ 
{rw heq at h, dsimp at h, rw cons_degree at h, rw cons_degree at h, 
have := @le_of_unbox_degree tl, 
cases (lt_or_eq_of_le this) with h₁ h₂,
{have hne : max (count_modal ψ) (modal_degree (unbox tl)) ≠ max (count_modal (box ψ)) (modal_degree tl), 
  { apply ne_of_lt, apply max_lt_of_lt, {simp, exact dec_trivial}, {exact h₁} },
contradiction },
{rw [h₂, zero_degree_of_eq_unbox h₂] at h, 
have : max (count_modal ψ) 0 < max (count_modal (box ψ)) 0,
  {simp [_root_.max], by_cases hz : count_modal ψ = 0,
   repeat {simp [hz], exact dec_trivial} },
have hne := ne_of_lt this, contradiction } },
case nnf.dia : ψ 
{rw heq at h, dsimp at h, rw cons_degree at h, 
have := @le_of_unbox_degree tl, 
cases (lt_or_eq_of_le this) with h₁ h₂,
{have hne : modal_degree (unbox tl) ≠ max (count_modal (box ψ)) (modal_degree tl),
  { apply ne_of_lt, exact lt_max_of_lt_right h₁ },
contradiction },
{have : modal_degree (unbox tl) < max (count_modal (dia ψ)) (modal_degree tl),
  {rw [h₂, zero_degree_of_eq_unbox h₂], 
   simp [_root_.max], apply nat.succ_pos},
have hne := ne_of_lt this, contradiction } },
case nnf.var : ψ
{rw heq at h, dsimp at h, rw cons_degree at h, 
 have hle : 0 ≤ modal_degree tl, { simp }, 
 have hz : modal_degree tl = 0, {apply zero_degree_of_eq_unbox, dsimp [_root_.max] at h, rw h, apply if_pos hle },
 rw cons_degree, simp [_root_.max, hz] },
case nnf.neg : ψ
{rw heq at h, dsimp at h, rw cons_degree at h, 
 have hle : 0 ≤ modal_degree tl, { simp }, 
 have hz : modal_degree tl = 0, {apply zero_degree_of_eq_unbox, dsimp [_root_.max] at h, rw h, apply if_pos hle },
 rw cons_degree, simp [_root_.max, hz] },
case nnf.and : ψ₁ ψ₂
{rw heq at h, dsimp at h, rw cons_degree at h, 
 by_cases hc : count_modal (and ψ₁ ψ₂) = 0,
 {rw hc at h, 
  have hle : 0 ≤ modal_degree tl, { simp }, 
  have hz : modal_degree tl = 0, {apply zero_degree_of_eq_unbox, dsimp [_root_.max] at h, rw h, apply if_pos hle },
  rw cons_degree, simp [_root_.max, hc, hz] }, -- eq case end
 {have := @le_of_unbox_degree tl, 
  cases (lt_or_eq_of_le this) with h₁ h₂,
  {have hne : modal_degree (unbox tl) ≠ max (count_modal (and ψ₁ ψ₂)) (modal_degree tl),
  { apply ne_of_lt, exact lt_max_of_lt_right h₁ },
contradiction }, 
  {have : modal_degree (unbox tl) < max (count_modal (and ψ₁ ψ₂)) (modal_degree tl), 
   {rw [h₂, zero_degree_of_eq_unbox h₂], 
    apply lt_max_of_lt_left, exact nat.pos_of_ne_zero hc},
   have hne := ne_of_lt this, contradiction} } }, -- lt case end
case nnf.or : ψ₁ ψ₂
{rw heq at h, dsimp at h, rw cons_degree at h, 
 by_cases hc : count_modal (or ψ₁ ψ₂) = 0,
 {rw hc at h, 
  have hle : 0 ≤ modal_degree tl, { simp }, 
  have hz : modal_degree tl = 0, {apply zero_degree_of_eq_unbox, dsimp [_root_.max] at h, rw h, apply if_pos hle },
  rw cons_degree, simp [_root_.max, hc, hz] },
 {have := @le_of_unbox_degree tl, 
  cases (lt_or_eq_of_le this) with h₁ h₂,
  {have hne : modal_degree (unbox tl) ≠ max (count_modal (and ψ₁ ψ₂)) (modal_degree tl),
  { apply ne_of_lt, exact lt_max_of_lt_right h₁ },
contradiction }, 
  {have : modal_degree (unbox tl) < max (count_modal (and ψ₁ ψ₂)) (modal_degree tl), 
   {rw [h₂, zero_degree_of_eq_unbox h₂], 
    apply lt_max_of_lt_left, exact nat.pos_of_ne_zero hc},
   have hne := ne_of_lt this, contradiction} } }
end

theorem unbox_degree_aux : Π {Γ φ}, dia φ ∈ Γ → modal_degree (unbox Γ) < modal_degree Γ
| [] φ h := absurd h $ not_mem_nil _
| (hd::tl) φ h := 
begin
cases heq : hd,
case nnf.box : ψ 
{dsimp, rw cons_degree, rw cons_degree,
apply max_lt_of_lt, 
{ simp, exact dec_trivial }, 
{ apply unbox_degree_aux, swap, exact φ, 
  cases h, {rw heq at h, contradiction}, {exact h} } },
case nnf.dia : ψ 
{dsimp [-modal_degree], rw cons_degree, 
have := @le_of_unbox_degree tl, 
cases (lt_or_eq_of_le this) with h₁ h₂,
{apply lt_max_of_lt_right h₁},
{rw [h₂, zero_degree_of_eq_unbox h₂], simp [_root_.max], apply nat.succ_pos} },
all_goals 
{dsimp [-modal_degree], rw cons_degree, 
apply lt_max_of_lt_right, apply unbox_degree_aux, swap, exact φ,
cases h, { rw heq at h, contradiction}, {exact h} }
end

theorem unbox_degree : Π {Γ φ}, dia φ ∈ Γ → 
                     modal_degree (φ :: unbox Γ) < modal_degree Γ
| [] φ h := absurd h $ not_mem_nil _
| (hd::tl) φ h := 
begin
rw cons_degree, apply max_lt,
{apply lt_of_lt_of_le, swap 3, exact count_modal (dia φ), simp, exact dec_trivial, apply mem_degree, exact h},
{apply unbox_degree_aux, exact h}
end

@[simp] def undia : list nnf → list nnf
| [] := []
| ((dia φ) :: l) := φ :: undia l
| (e :: l) := undia l

theorem undia_iff : Π {Γ φ}, dia φ ∈ Γ ↔ φ ∈ undia Γ
| [] φ := begin split, repeat {intro h, simpa using h} end
| (hd::tl) φ := 
begin
  split,
  { intro h, cases h₁ : hd, 
    case nnf.dia : ψ 
    { dsimp [undia], cases h, 
       {left, rw h₁ at h, injection h},
       {right, exact (@undia_iff tl φ).1 h} },
    all_goals 
    { dsimp [undia], cases h, 
       {rw h₁ at h, contradiction},
       {exact (@undia_iff tl φ).1 h} } },
  { intro h, cases h₁ : hd, 
    case nnf.dia : ψ
    { rw h₁ at h, dsimp [undia] at h, cases h, 
       {simp [h]}, {right, exact (@undia_iff tl φ).2 h} },
    all_goals 
    { rw h₁ at h, dsimp [undia] at h, right, exact (@undia_iff tl φ).2 h } }
end

theorem undia_degree : Π {Γ φ}, φ ∈ undia Γ → 
                     modal_degree (φ :: unbox Γ) < modal_degree Γ
:= 
begin
  intros Γ φ h,
  rw ←undia_iff at h,
  apply unbox_degree h
end

def get_contra : Π Γ : list nnf, 
                 psum {p : nat // var p ∈ Γ ∧ neg p ∈ Γ} 
                      (∀ n, var n ∈ Γ → neg n ∉ Γ)
| []             := psum.inr $ λ _ h, absurd h $ not_mem_nil _
| (hd :: tl)     := 
begin
  cases h : hd,
  case nnf.var : n 
  {apply dite (neg n ∈ tl),
    {intro t, 
     exact psum.inl ⟨n, ⟨mem_cons_self _ _, mem_cons_of_mem _ t⟩⟩},
    {intro e, 
     cases (get_contra tl),
     {left, constructor, constructor,
     apply mem_cons_of_mem, exact val.2.1,
     apply mem_cons_of_mem, exact val.2.2},
     {right,
      intros m hm hin, 
      by_cases eq : m=n,
      {apply e, cases hin, contradiction, rw ←eq, assumption},
      {cases hm, apply eq, injection hm, apply val, exact hm, 
       cases hin, contradiction, assumption} } }
  },
  case nnf.neg : n 
  { apply dite (var n ∈ tl),
    { intro t, 
      exact psum.inl ⟨n, ⟨mem_cons_of_mem _ t, mem_cons_self _ _⟩⟩ },
    { intro e, 
      cases (get_contra tl),
      {left, constructor, constructor,
      apply mem_cons_of_mem, exact val.2.1,
      apply mem_cons_of_mem, exact val.2.2 },
      { right,
        intros m hm hin, 
        by_cases eq : m=n,
        { apply e, cases hm, contradiction, rw ←eq, assumption },
        { cases hin, apply eq, injection hin, apply val, 
          swap, exact hin, cases hm, contradiction, assumption } 
      } 
    }
  },
  all_goals
  { 
  cases (get_contra tl),
  { left, constructor, constructor,
    apply mem_cons_of_mem, exact val.2.1,
    apply mem_cons_of_mem, exact val.2.2  },
  { right,
    intros m hm hin, 
    {apply val, swap 3, exact m, 
    cases hm, contradiction, assumption,
    cases hin, contradiction, assumption} }
  }
end

def get_contra_seqt : Π Γ : seqt,
                 psum {p : nat // var p ∈ Γ.main ∧ neg p ∈ Γ.main} 
                      (∀ n, var n ∈ Γ.main → neg n ∉ Γ.main)
:= λ Γ, get_contra Γ.main

def get_and : Π Γ : list nnf, 
              psum {p : nnf × nnf // and p.1 p.2 ∈ Γ} 
                   (∀ φ ψ, nnf.and φ ψ ∉ Γ)
| []               := psum.inr $ λ _ _, not_mem_nil _
| (hd :: tl)       := 
begin
  cases h : hd,
  case nnf.and : φ ψ { left, constructor,swap,
                       constructor, exact φ, exact ψ, simp
                     },
  all_goals 
  { cases (get_and tl),
    {left,
    constructor,
    apply mem_cons_of_mem,
    exact val.2},
    {right, intros γ ψ h, 
     cases h, contradiction,
    apply val, assumption }
  }
end

def get_and_seqt : Π Γ : seqt, 
              psum {p : nnf × nnf // and p.1 p.2 ∈ Γ.main} 
                   (∀ φ ψ, nnf.and φ ψ ∉ Γ.main)
:= λ Γ, get_and Γ.main

def get_or : Π Γ : list nnf, 
              psum {p : nnf × nnf // or p.1 p.2 ∈ Γ} 
                   (∀ φ ψ, nnf.or φ ψ ∉ Γ)
| []               := psum.inr $ λ _ _, not_mem_nil _
| (hd :: tl)       :=
begin
  cases h : hd,
  case nnf.or : φ ψ { left, constructor,swap,
                       constructor, exact φ, exact ψ, simp },
  all_goals 
  { cases (get_or tl),
    {left,
    constructor,
    apply mem_cons_of_mem,
    exact val.2},
    {right, intros γ ψ h, 
     cases h, contradiction,
    apply val, assumption}
  }
end

def get_or_seqt : Π Γ : seqt,
              psum {p : nnf × nnf // or p.1 p.2 ∈ Γ.main} 
                   (∀ φ ψ, nnf.or φ ψ ∉ Γ.main)
:= λ Γ, get_or Γ.main

def get_dia : Π Γ : list nnf, 
              psum {p : nnf // dia p ∈ Γ} 
                   (∀ φ, nnf.dia φ ∉ Γ)
| []               := psum.inr $ λ _, not_mem_nil _
| (hd :: tl)       := 
begin
  cases h : hd,
  case nnf.dia : φ { left, constructor, swap, exact φ, simp },
  all_goals 
  { cases (get_dia tl),
    {left,
    constructor,
    apply mem_cons_of_mem,
    exact val.2},
    {right, intros γ h, 
     cases h, contradiction,
     apply val, assumption } }
end

def get_dia_seqt : Π Γ : seqt,
              psum {p : nnf // dia p ∈ Γ.main} 
                   (∀ φ, nnf.dia φ ∉ Γ.main)
:= λ Γ, get_dia Γ.main


