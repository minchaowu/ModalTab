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

theorem pmapp {p : β → Prop} {q : α → Prop} (f : Π a, q a → β)  : Π (l : list α) 
(h : ∀ y (hy : q y) (h₁ : y ∈ l), p (f y hy)) 
(hf : ∀ y ∈ l, q y) x, x ∈ list.pmap f l hf → p x
| [] h hf x := by simp
| (hd::tl) h hf x := 
begin
  intro hmem, 
  cases hmem,
  {rw hmem, apply h, simp},
  {apply pmapp tl, intros a ha hamem, 
   apply h, simp [ha], right, exact hamem, exact hmem}
end

@[simp] def ne_empty_head : Π l : list α, l ≠ [] → α
| []       h := by contradiction
| (a :: l) h := a

theorem mem_pmap_of_mem {p : α → Prop} (f : Π a, p a → β) {a : α} {l : list α} (h : a ∈ l) (hf : ∀ y ∈ l, p y) : 
f a (hf a h) ∈ pmap f l hf :=
begin
  induction l with b l' ih,
  {cases h},
  {rcases h with rfl | h,
    {exact or.inl rfl},
    {apply or.inr,
     have hpy : ∀ (y : α), y ∈ l' → p y, 
       {intros y hy, apply hf, right, exact hy},
     have := ih h hpy, exact this}}
end

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

@[simp] def rebox : list nnf → list nnf 
| [] := []
| (hd::tl) := box hd :: rebox tl

theorem rebox_unbox_of_mem : Π {Γ} (h : ∀ {φ}, φ ∈ unbox Γ → box φ ∈ Γ), rebox (unbox Γ) ⊆ Γ
| [] h := by simp
| (hd::tl) h := 
begin
  cases hψ : hd,
  case nnf.box : φ {dsimp, simp [cons_subset_cons], apply subset_cons_of_subset, apply rebox_unbox_of_mem, simp [unbox_iff]},
  all_goals {dsimp, apply subset_cons_of_subset, apply rebox_unbox_of_mem, simp [unbox_iff]}
end

theorem unbox_rebox : Π {Γ}, unbox (rebox Γ) = Γ
| [] := by simp
| (hd::tl) := by simp [unbox_rebox]

-- Just that I don't want to say ∃ φ s.t. ...
def box_only_rebox : Π {Γ}, box_only (rebox Γ)
| [] := {no_var := by simp, 
         no_neg := by simp, 
         no_and := by simp, 
         no_or  := by simp, 
         no_dia := by simp}
| (hd::tl) := 
begin
  cases h : hd,
  all_goals {
  exact { no_var := begin 
                      intros n h, cases h, contradiction, 
                      apply (@box_only_rebox tl).no_var, assumption 
                    end, 
          no_neg := begin 
                      intros n h, cases h, contradiction, 
                      apply (@box_only_rebox tl).no_neg, assumption 
                    end,
          no_and := begin 
                      intros φ ψ h, cases h, contradiction, 
                      apply (@box_only_rebox tl).no_and, assumption 
                    end,
          no_or := begin 
                     intros φ ψ h, cases h, contradiction, 
                     apply (@box_only_rebox tl).no_or, assumption 
                   end, 
          no_dia := begin 
                      intros φ h, cases h, contradiction, 
                      apply (@box_only_rebox tl).no_dia, assumption 
                    end} }
end

theorem rebox_iff : Π {φ Γ}, box φ ∈ rebox Γ ↔ φ ∈ Γ
| φ [] := by simp
| φ (hd::tl) := 
begin
  split, 
  {intro h, cases h₁ : hd, 
   all_goals { cases h, 
               {left, rw ←h₁, injection h}, 
               {right,  have := (@rebox_iff φ tl).1, exact this h } }},
  {intro h, cases h₁ : hd, 
   all_goals { dsimp, cases h, 
               {left, rw ←h₁, rw h}, 
               {right, have := (@rebox_iff φ tl).2, exact this h } } }
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

def get_contra_seqt : Π Γ : sseqt,
                 psum {p : nat // var p ∈ Γ.m ∧ neg p ∈ Γ.m} 
                      (∀ n, var n ∈ Γ.m → neg n ∉ Γ.m)
:= λ Γ, get_contra Γ.m

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

def get_and_seqt : Π Γ : sseqt, 
              psum {p : nnf × nnf // and p.1 p.2 ∈ Γ.m} 
                   (∀ φ ψ, nnf.and φ ψ ∉ Γ.m)
:= λ Γ, get_and Γ.m

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

def get_or_seqt : Π Γ : sseqt,
              psum {p : nnf × nnf // or p.1 p.2 ∈ Γ.m} 
                   (∀ φ ψ, nnf.or φ ψ ∉ Γ.m)
:= λ Γ, get_or Γ.m

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

def get_dia_seqt : Π Γ : sseqt,
              psum {p : nnf // dia p ∈ Γ.m} 
                   (∀ φ, nnf.dia φ ∉ Γ.m)
:= λ Γ, get_dia Γ.m

def get_box : Π Γ : list nnf,
              psum {l : nnf // box l ∈ Γ} 
                   (∀ φ, nnf.box φ ∉ Γ)
| [] := psum.inr $ λ _, not_mem_nil _
| (hd :: tl) := 
begin
  cases h : hd,
  case nnf.box : φ { left, constructor, swap, exact φ, simp },
  all_goals 
  { cases (get_box tl),
    {left,
    constructor,
    apply mem_cons_of_mem,
    exact val.2},
    {right, intros γ h, 
     cases h, contradiction,
     apply val, assumption } }
end

def get_box_seqt : Π Γ : sseqt,
              psum {p : nnf // box p ∈ Γ.m} 
                   (∀ φ, nnf.box φ ∉ Γ.m)
:= λ Γ, get_box Γ.m

@[simp] def get_var : list nnf → list ℕ
| [] := []
| ((var n) :: l) := n :: get_var l
| (e :: l) := get_var l

theorem get_var_iff : Π {Γ n}, var n ∈ Γ ↔ n ∈ get_var Γ
| [] φ := begin split, repeat {intro h, simpa using h} end
| (hd::tl) φ := 
begin
  split,
  { intro h, cases h₁ : hd, 
    case nnf.var : n
    { dsimp, cases h, 
       {left, rw h₁ at h, injection h},
       {right, exact (@get_var_iff tl φ).1 h} },
    all_goals 
    { dsimp, cases h, 
       {rw h₁ at h, contradiction},
       {exact (@get_var_iff tl φ).1 h} } },
  { intro h, cases h₁ : hd, 
    case nnf.var : n
    { rw h₁ at h, dsimp at h, cases h, 
       {simp [h]}, {right, exact (@get_var_iff tl φ).2 h} },
    all_goals 
    { rw h₁ at h, dsimp [undia] at h, right, exact (@get_var_iff tl φ).2 h } }
end
