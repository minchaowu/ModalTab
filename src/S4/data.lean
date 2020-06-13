import defs data.list.perm
open nnf

namespace list
universes u v w
variables {α : Type u}

theorem length_sub_lt_of_nodup_subperm [decidable_eq α] {l₁ l₂ : list α} {a : α} 
(h₁ : l₁ <+~ l₂) (h₂ : a ∈ l₂) (h₃ : a ∉ l₁) (h₄ : nodup l₁):
length l₂ - length (a :: l₁) < length l₂ - length l₁
:=
begin
  rw nat.sub_lt_sub_left_iff,
  { simp [zero_lt_one] }, 
  { apply subperm.length_le, 
    apply cons_subperm_of_mem; assumption }
end

end list

structure psig : Type :=
(d : nnf)
(b : list nnf)

instance : decidable_eq psig := by tactic.mk_dec_eq_instance

def sig : Type := option psig

instance : decidable_eq sig := by tactic.mk_dec_eq_instance

def dsig : Π (s : sig) (h : s ≠ none), nnf
| none h := by contradiction
| (some ⟨d, b⟩) h := d

def bsig : Π (s : sig) (h : s ≠ none), list nnf
| none h := by contradiction
| (some ⟨d, b⟩) h := b

instance (Γ) : decidable_eq (no_literals Γ) := by tactic.mk_dec_eq_instance

instance (Γ) : decidable_eq (saturated Γ) := by tactic.mk_dec_eq_instance

instance (Γ) : decidable_eq (box_only Γ) := by tactic.mk_dec_eq_instance

structure sseqt : Type :=
(goal : list nnf)
(s : sig) -- sig := option psig
(a : list psig) -- psig is the signature, which is of the form (d, b)
(h b m: list nnf)
(ndh : list.nodup h) -- nodup says there is no duplicate elements
(ndb : list.nodup b)
(sph : h <+~ closure goal) -- <+~ denotes sublist permutation
(spb : b <+~ closure goal)
(sbm : m ⊆ closure goal)
(ha : ∀ φ ∈ h, (⟨φ, b⟩ : psig) ∈ a)
(hb : box_only b)
-- dsig takes a signature (d, b) and a proof h, and returns d
(ps₁ : Π (h : s ≠ none), dsig s h ∈ m)
-- bsig takes a signature (d, b) and a proof h, and returns b
(ps₂ : Π (h : s ≠ none), bsig s h ⊆ m)

instance : decidable_eq sseqt := by tactic.mk_dec_eq_instance

class val_constructible (Γ : sseqt) :=
(satu : saturated Γ.m)
(no_box_main : ∀ {φ}, box φ ∉ Γ.m)
(no_contra_main : ∀ {n}, var n ∈ Γ.m → neg n ∉ Γ.m)

class modal_applicable (Γ : sseqt) extends val_constructible Γ :=
(φ : nnf)
(ex : dia φ ∈ Γ.m)

class model_constructible (Γ : sseqt) extends val_constructible Γ :=
(no_dia : ∀ {φ}, nnf.dia φ ∉ Γ.m)

def and_child {φ ψ} (Γ : sseqt) (h : nnf.and φ ψ ∈ Γ.m) : sseqt :=
{ goal := Γ.goal, 
  s := none,
  m := φ :: ψ :: Γ.m.erase (and φ ψ),
  sbm := begin 
          intros x hx, cases hx, 
          {rw hx, apply (mem_closure_and _ (Γ.sbm h)).1}, 
          {cases hx, 
           {rw hx, apply (mem_closure_and _ (Γ.sbm h)).2},
           {apply Γ.sbm, apply list.erase_subset, exact hx}}
         end,
  ps₁ := by intro; contradiction,
  ps₂ := by intro; contradiction,
  .. Γ}

inductive and_instance_seqt (Γ : sseqt) : sseqt → Type
| cons : Π {φ ψ} (h : nnf.and φ ψ ∈ Γ.m), 
         and_instance_seqt $ and_child Γ h

def or_child_left {φ ψ} (Γ : sseqt) (h : nnf.or φ ψ ∈ Γ.m) : sseqt :=
{ goal := Γ.goal, 
  s := none,
  m := φ :: Γ.m.erase (or φ ψ),
  sbm := begin 
          intros x hx, cases hx, 
          {rw hx, apply (mem_closure_or _ (Γ.sbm h)).1}, 
          {apply Γ.sbm, apply list.erase_subset, exact hx}
         end,
  ps₁ := by intro; contradiction,
  ps₂ := by intro; contradiction,
  .. Γ}

def or_child_right {φ ψ} (Γ : sseqt) (h : nnf.or φ ψ ∈ Γ.m) : sseqt :=
{ goal := Γ.goal, 
  s := none,
  m := ψ :: Γ.m.erase (or φ ψ),
  sbm := begin 
           intros x hx, cases hx, 
           {rw hx, apply (mem_closure_or _ (Γ.sbm h)).2}, 
           {apply Γ.sbm, apply list.erase_subset, exact hx}
         end,
  ps₁ := by intro; contradiction,
  ps₂ := by intro; contradiction,
  .. Γ}

inductive or_instance_seqt (Γ : sseqt) : sseqt → sseqt → Type
| cons : Π {φ ψ} (h : nnf.or φ ψ ∈ Γ.m),
         or_instance_seqt (or_child_left Γ h) (or_child_right Γ h)

def box_child_new {φ} (Γ : sseqt) (h₁ : nnf.box φ ∈ Γ.m) (h₂ : nnf.box φ ∉ Γ.b) : sseqt :=
{ goal := Γ.goal, 
  s := none,
  h := [], 
  b := box φ :: Γ.b, 
  m := φ :: Γ.m.erase (box φ),
  ndh := by simp,
  ndb := begin rw list.nodup_cons, split, exact h₂, exact Γ.ndb end,
  sph := begin apply list.nil_subperm end,
  spb := begin 
           apply list.cons_subperm_of_mem Γ.ndb h₂, 
           apply Γ.sbm h₁, apply Γ.spb
         end,
  sbm := begin 
           intros x hx, cases hx, 
           {rw hx, apply mem_closure_box _ (Γ.sbm h₁)}, 
           {apply Γ.sbm, apply list.erase_subset, exact hx}
         end,
  ha := λ φ h, absurd h $ list.not_mem_nil _,
  hb := cons_box_only Γ.hb,
  ps₁ := by intro; contradiction,
  ps₂ := by intro; contradiction,
  .. Γ}

inductive box_new_instance_seqt (Γ : sseqt) : sseqt → Type
| cons : Π {φ} (h₁ : nnf.box φ ∈ Γ.m) (h₂ : nnf.box φ ∉ Γ.b), 
         box_new_instance_seqt $ box_child_new Γ h₁ h₂

def box_child {φ} (Γ : sseqt) (h₁ : nnf.box φ ∈ Γ.m) : sseqt :=
{ goal := Γ.goal, 
  s := none,
  a := Γ.a, 
  h := Γ.h, 
  b := Γ.b, 
  m := φ :: Γ.m.erase (box φ),
  ndh := Γ.ndh,
  ndb := Γ.ndb,
  sph := Γ.sph,
  spb := Γ.spb,
  sbm := begin 
           intros x hx, cases hx, 
           {rw hx, apply mem_closure_box _ (Γ.sbm h₁)}, 
           {apply Γ.sbm, apply list.erase_subset, exact hx}
         end,
  ha := Γ.ha,
  hb := Γ.hb,
  ps₁ := by intro; contradiction,
  ps₂ := by intro; contradiction}

inductive box_dup_instance_seqt (Γ : sseqt) : sseqt → Type
| cons : Π {φ} (h₁ : nnf.box φ ∈ Γ.m) (h₂ : nnf.box φ ∈ Γ.b), 
         box_dup_instance_seqt $ box_child Γ h₁


theorem hintikka_vc {Γ} (h : val_constructible Γ) : hintikka Γ.m :=
{hno_contra := h.no_contra_main,
 hand_left := begin intros φ ψ h₁, exfalso, apply h.satu.no_and, exact h₁ end,
 hand_right := begin intros φ ψ h₁, exfalso, apply h.satu.no_and, exact h₁ end,
 hor := begin intros φ ψ h₁, exfalso, apply h.satu.no_or, exact h₁ end,
 hbox := begin intros φ h₁, exfalso, apply h.no_box_main, exact h₁ end}

theorem hintikka_ma {Γ} (h : modal_applicable Γ) : hintikka Γ.m :=
hintikka_vc h.to_val_constructible

theorem hintikka_mc {Γ} (h : model_constructible Γ) : hintikka Γ.m :=
hintikka_vc h.to_val_constructible

structure info : Type :=
(id : sseqt)
(htk : list nnf)
(hhtk : hintikka htk)
(mhtk : id.m ⊆ htk)

instance : decidable_eq info := by tactic.mk_dec_eq_instance

inductive tmodel
| cons : info → list tmodel → list psig → tmodel

instance : decidable_eq tmodel := by tactic.mk_dec_eq_instance
