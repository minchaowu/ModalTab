/-
Copyright (c) 2018-2019 Minchao Wu. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Minchao Wu
-/

import defs data.list.perm .data
open nnf tactic

meta def frame_restriction : tactic unit :=
do intro `a >> `[simp]

structure S4 (states : Type) extends kripke states :=
(refl  : reflexive rel . frame_restriction)
(trans : transitive rel . frame_restriction)

instance inhabited_S4 : inhabited (S4 ℕ) := 
⟨ { val := λ a b, tt, rel := λ a b, tt } ⟩

@[simp] def force {states : Type} (k : S4 states) : states → nnf → Prop
| s (var n)    := k.val n s
| s (neg n)    := ¬ k.val n s
| s (and φ ψ)  := force s φ ∧ force s ψ
| s (or φ ψ)   := force s φ ∨ force s ψ
| s (box φ)    := ∀ s', k.rel s s' → force s' φ
| s (dia φ)    := ∃ s', k.rel s s' ∧ force s' φ

def sat {st} (k : S4 st) (s) (Γ : list nnf) : Prop := 
∀ φ ∈ Γ, force k s φ

def unsatisfiable (Γ : list nnf) : Prop := 
∀ (st) (k : S4 st) s, ¬ sat k s Γ

theorem unsat_singleton {φ} : unsatisfiable [φ] → ∀ (st) (k : S4 st) s, ¬ force k s φ
 := 
begin
  intros h _ _ _ hf,
  apply h, intros ψ hψ, rw list.mem_singleton at hψ, rw hψ, exact hf
end

theorem sat_of_empty {st} (k : S4 st) (s) : sat k s [] :=
λ φ h, absurd h $ list.not_mem_nil _

theorem ne_empty_of_unsat {Γ} (h : unsatisfiable Γ): Γ ≠ [] := 
begin 
  intro heq, rw heq at h, 
  apply h, apply sat_of_empty, exact nat, 
  apply inhabited_S4.1, exact 0 
end

open tmodel

@[simp] def minfo : Π m : tmodel, info
| (cons i l ba) := i

@[simp] def htk : Π m : tmodel, list nnf
| (cons i l ba) := i.htk

def hist : Π m : tmodel, list nnf
| (cons i l ba) := i.id.h

@[simp] def msig : Π m : tmodel, sig
| (cons i l ba) := i.id.s

@[simp] def manc : Π m : tmodel, list psig
| (cons i l ba) := i.id.a

def bhist : Π m : tmodel, list nnf
| (cons i l ba) := i.id.b

@[simp] def request : Π m : tmodel, list psig
| (cons i l ba) := ba

@[simp] def proper_request_box : Π m : tmodel, Prop
| (cons i l ba) := ∀ rq : psig, rq ∈ ba → ∀ φ, (box φ ∈ i.htk ∨ box φ ∈ i.id.b) → box φ ∈ rq.b

@[simp] def subset_request : Π m : tmodel, Prop
| (cons i l ba) := ba ⊆ i.id.a

@[simp] def tmodel_step_bhist : Π m : tmodel, Prop 
| m@(cons i l ba) := ∀ s ∈ l, ∀ φ, box φ ∈ i.id.b → box φ ∈ htk s

@[simp] def tmodel_step_box : Π m : tmodel, Prop 
| m@(cons i l ba) := ∀ s ∈ l, ∀ φ, box φ ∈ i.htk → box φ ∈ htk s

-- Can be strenghtened
@[simp] def tmodel_dia : Π m : tmodel, Prop 
| m@(cons i l ba) := ∀ φ, dia φ ∈ i.htk → (∃ rq : psig, rq ∈ ba ∧ rq.d = φ) ∨ ∃ s ∈ l, φ ∈ htk s

@[simp] def child : tmodel → tmodel → bool
| s (cons i l ba) := s ∈ l

inductive tc' {α : Type} (r : α → α → Prop) : α → α → Prop
| base : ∀ a b, r a b → tc' a b
| step : ∀ a b c, r a b → tc' b c → tc' a c

theorem tc'.trans {α : Type} {r : α → α → Prop} {a b c : α} : 
tc' r a b → tc' r b c → tc' r a c :=
begin
intros h₁ h₂,
induction h₁,
apply tc'.step, exact h₁_a_1, exact h₂,
apply tc'.step, exact h₁_a_1, apply h₁_ih, exact h₂
end

def desc : tmodel → tmodel → Prop := tc' (λ s m, child s m)

theorem desc_not_nil : Π c i ba m, m = cons i [] ba → desc c m → false :=
begin
intros c i ba m heq h,
induction h,
{rw heq at h_a_1, simp at h_a_1, exact h_a_1},
{apply h_ih, exact heq}
end

theorem desc_iff_eq_child_aux : Π i₁ i₂ s₁ s₂ l₁ l₂ m₁ m₂ m₃, 
m₁ = cons i₁ l₁ s₁ → m₂ = cons i₂ l₂ s₂ → l₁ = l₂ → 
(desc m₃ m₁ ↔ desc m₃ m₂) :=
begin
intros i₁ i₂ s₁ s₂ l₁ l₂ m₁ m₂ m₃ heq₁ heq₂ heq,
split,
{intro hd, induction hd,
 {rw heq₁ at hd_a_1, simp at hd_a_1,
 rw heq at hd_a_1,
 apply tc'.base, rw heq₂, simp, exact hd_a_1},
 {apply tc'.trans, apply tc'.base, exact hd_a_1, apply hd_ih, exact heq₁}},
{intro hd, induction hd,
 {rw heq₂ at hd_a_1, simp at hd_a_1,
 rw ←heq at hd_a_1,
 apply tc'.base, rw heq₁, simp, exact hd_a_1},
 {apply tc'.trans, apply tc'.base, exact hd_a_1, apply hd_ih, exact heq₂}}
end

theorem eq_desc_of_eq_children {i₁ i₂ s₁ s₂ l c} : 
desc c (cons i₁ l s₁) = desc c (cons i₂ l s₂) :=
begin rw desc_iff_eq_child_aux, repeat {refl} end 

theorem desc_step : Π c i l ba, c ∈ l → desc c (cons i l ba)
| c i [] ba h := absurd h $ list.not_mem_nil _
| c i (hd::tl) ba h := 
begin
constructor,
simp, cases h,
left, exact h, right, exact h
end

theorem desc_ex : Π c i l ba, (∃ m ∈ l, desc c m) → desc c (cons i l ba)
| c i [] ba h := begin rcases h with ⟨w, hmem, hw⟩, exact (absurd hmem $ list.not_mem_nil _) end
| c i (hd::tl) ba h := 
begin
rcases h with ⟨w, hmem, hw⟩,
cases hw,
{apply tc'.step,
swap 3, {exact w},
{exact hw_a_1},
{apply tc'.base, simp, cases hmem, left, exact hmem, right, exact hmem}},
{apply tc'.step, exact hw_a_1, apply tc'.trans, exact hw_a_2, apply tc'.base, simp, exact hmem}
end

theorem ex_desc : Π c i l ba m, m = (cons i l ba) → desc c m → (c ∈ l ∨ ∃ m ∈ l, desc c m) := 
begin
intros c i l ba m heq h,
induction h,
{left, rw heq at h_a_1, simp at h_a_1, exact h_a_1},
{cases h_ih heq,
 {right, split, split, exact h, apply tc'.base, exact h_a_1},
 {rcases h with ⟨w, hmem, hw⟩, right, split, split, exact hmem, apply tc'.step, exact h_a_1, exact hw}}
end

theorem ex_desc' : Π c i l ba, desc c (cons i l ba) → (c ∈ l ∨ ∃ m ∈ l, desc c m) := 
begin intros c i l ba h, apply ex_desc, repeat {refl}, exact h end

@[simp] def tmodel_anc : Π m : tmodel, Prop 
| m@(cons i l ba) := ∀ s rq, desc s m → rq ∈ request s →  
                     (rq ∈ manc m) ∨
                     (∃ d, desc d m ∧ some rq = msig d)

structure ptmodel (m : tmodel) : Prop :=
(bhist : tmodel_step_bhist m)
(sbox : tmodel_step_box m)
(pdia : tmodel_dia m)
(bdia : tmodel_anc m)
(reqb : proper_request_box m)
(sreq : subset_request m)

def global_pt (m : tmodel) := ∀ s, desc s m → ptmodel s

open subtype

def model : Type := {m : tmodel // ptmodel m ∧ global_pt m}

def rmodel : Type := {m : tmodel // ptmodel m}

inductive reach_step : rmodel → rmodel → Prop
| fwd_base (s : rmodel) (i l ba h) : s.1 ∈ l → reach_step ⟨(cons i l ba), h⟩  s
| bwd_base (s : rmodel) (i l ba h) : (∃ rq ∈ ba, some rq = msig s.1) → reach_step ⟨(cons i l ba), h⟩ s

theorem reach_step_box (s₁ s₂ φ) (h₁ : reach_step s₁ s₂) (h₂ : box φ ∈ htk s₁.1) : box φ ∈ htk s₂.1 :=
begin
cases h₁,
{cases s₂ with s₂ ps₂,
 cases s₂ with i₂ l₂ sg₂,
 simp,
 have := h₁_h.sbox,
 simp at this, simp at h₂,
 have hmem := this _ h₁_a _ h₂,
 simp at hmem, exact hmem },
{cases s₂ with s₂ ps₂,
 cases s₂ with i₂ l₂ sg₂,
 simp,
 rcases h₁_a with ⟨w,hmem,hw⟩,
 simp at hw,
 apply i₂.mhtk,
 have := i₂.id.ps₂,
 rw ←hw at this,
 have hneq : some w ≠ none, 
   {intro heq, contradiction},
 have hsub := this hneq,
 apply hsub,
 have := h₁_h.reqb,
 simp at this, simp at h₂,
 have hc := this w hmem φ (or.inl h₂),
 cases w, 
 dsimp [bsig], exact hc}
end

inductive rtc {α : Type} (r : α → α → Prop) : α → α → Prop
| refl   : Π a, rtc a a
| step   : Π a b c, r a b → rtc b c → rtc a c

theorem rtc.trans {α : Type} {r : α → α → Prop} {a b c : α} : 
rtc r a b → rtc r b c → rtc r a c :=
begin
intros h₁ h₂,
induction h₁,
exact h₂,
apply rtc.step, exact h₁_a_1, apply h₁_ih, exact h₂
end

theorem rtc_step {α : Type} {r : α → α → Prop} {a b : α} (h : r a b) : 
rtc r a b :=
by apply rtc.step _ _ _ h; apply rtc.refl

def reach (s₁ s₂ : rmodel) := rtc reach_step s₁ s₂

theorem refl_reach : Π s, reach s s := λ s, rtc.refl s

theorem trans_reach : Π s₁ s₂ s₃, reach s₁ s₂ → reach s₂ s₃ → reach s₁ s₃ := λ s₁ s₂ s₃ h₁ h₂, rtc.trans h₁ h₂

@[simp] def builder (m : tmodel) : S4 {x : rmodel // x.1 = m ∨ desc x.1 m} := 
{val := λ v s, var v ∈ htk s.1.1, 
 rel := λ s₁ s₂, reach s₁ s₂, 
 refl := λ s, refl_reach s, 
 trans := λ a b c, trans_reach a b c}

open rtc

theorem reach_box (s₁ s₂ φ) (h₁ : reach s₁ s₂) (h₂ : box φ ∈ htk s₁.1) : φ ∈ htk s₂.1 :=
begin
induction h₁ with m m₁ m₂ m₃ h₁₂ h₂₃ ih, 
{cases m with tm hm, cases tm with i l sg,
simp,
apply i.hhtk.hbox,
simp at h₂, exact h₂},
{apply ih, 
 apply reach_step_box,
 exact h₁₂, exact h₂}
end

theorem reach_step_dia (s : rmodel) (rt : model) (φ) 
(h₁ : desc s.1 rt.1) 
(h₂ : manc rt.1 = []) (h₃ : dia φ ∈ htk s.1) : 
∃ s', reach_step s s' ∧ φ ∈ htk s'.1 ∧ desc s'.1 rt.1 :=
begin
cases s with s ps,
cases s with i l sg,
have := ps.pdia,
simp at this, simp at h₃,
have hc := this _ h₃,
cases hc,
{cases rt with rt prt,
 cases rt with irt lrt sgrt,
 rcases hc with ⟨w, hmem, hw⟩,
 have := prt.1.bdia,
 simp at this, simp at h₁,
 have hcaux := this _ w h₁,
 simp at hcaux,
 have hcc := hcaux hmem,
 simp at h₂,
 cases hcc,
 {rw h₂ at hcc, exfalso, apply list.not_mem_nil, exact hcc},
 {rcases hcc with ⟨m, hml, hmr⟩, 
  have pm := prt.2 m hml,
  split, split,
  swap 3, exact ⟨m, pm⟩,
  apply reach_step.bwd_base,
  split, split, exact hmem, simp, exact hmr,
  split,
  {cases m with im lm sgm, simp,
   apply im.mhtk, 
   have := im.id.ps₁,
   simp at hmr, rw ←hmr at this,
   have hneq : some w ≠ none, {intro, contradiction},
   have hmem := this hneq, 
   cases w, dsimp [dsig] at hmem,
   rw ←hw, exact hmem_1 },
  {exact hml} } },
{rcases hc with ⟨m, pml, pmr⟩,
 have hdm : desc m rt.1, 
  {apply tc'.trans, apply tc'.base, 
   swap 3, exact (⟨cons i l sg, ps⟩ : rmodel).val, 
   simp, exact pml, exact h₁},
 cases rt with rt prt,
 cases rt with irt lrt sgrt,
 have pm := prt.2 m hdm,
 split, split, swap 3,
 exact ⟨m, pm⟩,
 apply reach_step.fwd_base,
 exact pml, split,
 {exact pmr},
 {exact hdm} }
end

theorem reach_dia (s : rmodel) (rt : model) (φ) 
(h₁ : desc s.1 rt.1) 
(h₂ : manc rt.1 = []) (h₃ : dia φ ∈ htk s.1) : 
∃ s', reach s s' ∧ φ ∈ htk s'.1 ∧ desc s'.1 rt.1:=
begin
have := reach_step_dia s rt φ h₁ h₂ h₃,
rcases this with ⟨w, hwl, hwr⟩,
split, split, swap 3, exact w,
apply rtc_step hwl, exact hwr
end

theorem reach_step_dia_root (s : rmodel) (rt : model) (φ) 
(h₁ : s.1 = rt.1) 
(h₂ : manc rt.1 = []) (h₃ : dia φ ∈ htk s.1) : 
∃ s', reach_step s s' ∧ φ ∈ htk s'.1 ∧ desc s'.1 rt.1 :=
begin
cases s with s ps,
cases s with is ls sgs,
have := ps.pdia,
simp at this, simp at h₃,
have hc := this _ h₃,
cases hc,
{have := ps.sreq, simp at this, 
 rcases hc with ⟨w, hmw, hw⟩,
 have hmem := this hmw,
 cases rt with rt prt,
 rw ←h₁ at h₂,
 simp at h₂, rw h₂ at hmem,
 exfalso, apply list.not_mem_nil, exact hmem},
{cases rt with rt prt,
 rcases hc with ⟨w, hwl, hwr⟩,
 have ptw : ptmodel w, 
   {apply prt.2, apply tc'.base, simp at h₁, rw ←h₁, simp, exact hwl},
 split, split, swap 3, exact ⟨w, ptw⟩,
 apply reach_step.fwd_base, exact hwl, split, 
 {exact hwr}, 
 {apply tc'.base, simp, simp at h₁, rw ←h₁, simp, exact hwl} }
end

theorem reach_dia_root (s : rmodel) (rt : model) (φ) 
(h₁ : s.1 = rt.1) 
(h₂ : manc rt.1 = []) (h₃ : dia φ ∈ htk s.1) : 
∃ s', reach s s' ∧ φ ∈ htk s'.1 ∧ desc s'.1 rt.1 :=
begin
have := reach_step_dia_root s rt φ h₁ h₂ h₃,
rcases this with ⟨w, hwl, hwr⟩,
split, split, swap 3, exact w,
apply rtc_step hwl, exact hwr
end

theorem good_model (m : model) (hrt : manc m.1 = []): 
Π (s : {x : rmodel // x.1 = m.1 ∨ desc x.1 m.1}) (φ : nnf), 
  φ ∈ htk s.1.1 → force (builder m.1) s φ
| s (var n) h   := begin simp, exact h end
| s (neg n) h   := begin 
                     simp, intro hin, 
                     cases s with s ps,
                     cases s with s pts,
                     cases s with i l sg,
                     have := i.hhtk.hno_contra,
                     simp at hin,
                     apply this hin, simp at h, exact h
                   end
| s (and φ ψ) h := begin 
                   split,
                   {apply good_model, 
                   cases s with s ps,
                   cases s with s pts,
                   cases s with i l sg,
                   have := i.hhtk.hand_left,
                   simp, apply this, simp at h, exact h},
                   {apply good_model, 
                   cases s with s ps,
                   cases s with s pts,
                   cases s with i l sg,
                   have := i.hhtk.hand_right,
                   simp, apply this, simp at h, exact h}
                   end
| s (or φ ψ) h  := begin
                   cases s with s ps,
                   cases s with s pts,
                   cases s with i l sg,
                   have := i.hhtk.hor,
                   simp at h,
                   have hc := this h,
                   cases hc,
                   {simp, left, apply good_model, simp, exact hc},
                   {simp, right, apply good_model, simp, exact hc}
                   end
| s (box φ) h   := begin
                   intros m hm,
                   apply good_model,
                   apply reach_box,
                   exact hm,
                   exact h
                   end
| s (dia φ) h   := begin
                   cases s with s ps,
                   cases ps,
                   {simp, simp at h,
                    have := reach_dia_root _ _ _ ps hrt h,
                    rcases this with ⟨s', hs'l, hs'm, hs'r⟩,
                    split, split, 
                    exact hs'l, split, apply good_model, simp,
                    exact hs'm, right, exact hs'r },
                   {simp, simp at h,
                    have := reach_dia _ _ _ ps hrt h,
                    rcases this with ⟨s', hs'l, hs'm, hs'r⟩,
                    split, split, 
                    exact hs'l, split, apply good_model, simp,
                    exact hs'm, right, exact hs'r}
                   end
