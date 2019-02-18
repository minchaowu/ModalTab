import .marking
open nnf subtype list batch_sat

inductive node (Γ : list nnf) : Type
| closed : Π m, unsatisfiable Γ → pmark Γ m → node
| open_  : {s // sat builder s Γ} → node

open node

def and_rule {Γ Δ} (i : and_instance Γ Δ) : node Δ → node Γ
| (closed m h p) := begin 
                      left, 
                      {apply unsat_of_closed_and, repeat {assumption}}, 
                      exact (pmark_of_closed_and i m h p).2
                    end

| (open_ w)  := begin
                  right,
                  clear and_rule,
                  cases i with φ ψ h,
                  constructor,
                  exact sat_and_of_sat_split _ _ _ _ _ h w.2
                end

def jump_rule {Γ₁ Γ₂ Δ : list nnf} (i : or_instance Δ Γ₁ Γ₂) 
(m : list nnf) (h₁ : unsatisfiable Γ₁) (h₂ : pmark Γ₁ m) 
(h₃ : left_prcp i ∉ m) : node Δ := 
begin
  left,
  {apply unsat_of_jump, repeat {assumption}},
  exact (pmark_of_jump i m h₁ h₂ h₃).2
end

def or_rule {Γ₁ Γ₂ Δ} (i : or_instance Δ Γ₁ Γ₂) : 
  node Γ₁ → node Γ₂ → node Δ
| (open_ w) _ := begin
                   right,
                   clear or_rule,
                   cases i with φ ψ h,
                   constructor,
                   exact sat_or_of_sat_split_left _ _ _ _ _ h w.2
                 end
| _ (open_ w) := begin
                   right,
                   clear or_rule,
                   cases i with φ ψ h,
                   constructor,
                   exact sat_or_of_sat_split_right _ _ _ _ _ h w.2
                 end
| (closed m₁ h₁ p₁) (closed m₂ h₂ p₂):= 
                 begin 
                   left, 
                   {apply unsat_of_closed_or, repeat {assumption}}, 
                   exact (pmark_of_closed_or i h₁ p₁ h₂ p₂).2
                 end

def open_rule {Γ₁ Γ₂ Δ} {s} (i : or_instance Δ Γ₁ Γ₂) (h : sat builder s Γ₁) : node Δ :=
begin
  right, constructor,
  cases i with φ ψ hin, 
  swap, exact s,
  exact sat_or_of_sat_split_left _ _ _ _ _ hin h
end

def contra_rule {Δ n} (h : var n ∈ Δ ∧ neg n ∈ Δ) : node Δ := 
begin
  left,
  {exact unsat_contra h.1 h.2},
  swap,
  {exact [var n, neg n]},
  {intros Δ' hΔ' hsub, 
   apply unsat_contra,
   {apply mem_diff_of_mem,
   exact h.1, intro, apply hΔ' (var n) a, simp},
   {apply mem_diff_of_mem, 
   exact h.2, intro, apply hΔ' (neg n) a, simp} }
end

/-  This is essentially the modal rule. -/

-- def tmap {p : list nnf → Prop} (f : Π Γ, p Γ → node Γ): Π Γ : list $ list nnf, (∀ i∈Γ, p i) → 
-- psum ({i // i ∈ Γ ∧ unsatisfiable i}) {x : list model // batch_sat x Γ}
-- | [] h := psum.inr ⟨[], bs_nil⟩
-- | (hd :: tl) h := 
-- match f hd (h hd (by simp)) with
-- | (node.closed _ pr _) := psum.inl ⟨hd, by simp, pr⟩
-- | (node.open_ w₁) := 
--   match tmap tl (λ x hx, h x $ by simp [hx]) with
--   | (psum.inl uw) := begin 
--                        left, rcases uw with ⟨w, hin, h⟩, 
--                        split, split, swap, exact h, simp [hin]
--                      end
--   | (psum.inr w₂) := psum.inr ⟨(w₁.1::w₂), bs_cons _ _ _ _ w₁.2 w₂.2⟩
--   end
-- end

def tmap {p : list nnf → Prop} (f : Π Γ, p Γ → node Γ): Π Γ : list $ list nnf, (∀ i∈Γ, p i) → 
psum 
({ c : list nnf × list nnf // c.1 ∈ Γ ∧ unsatisfiable c.1 ∧ pmark c.1 c.2}) 
{x : list model // batch_sat x Γ}
| [] h := psum.inr ⟨[], bs_nil⟩
| (hd :: tl) h := 
match f hd (h hd (by simp)) with
| (node.closed m pr pm) := psum.inl ⟨⟨hd,m⟩, by simp, pr, pm⟩
| (node.open_ w₁) := 
  match tmap tl (λ x hx, h x $ by simp [hx]) with
  | (psum.inl uw) := begin 
                       left, rcases uw with ⟨w, hin, h⟩, 
                       split, split, swap, exact h, simp [hin]
                     end
  | (psum.inr w₂) := psum.inr ⟨(w₁.1::w₂), bs_cons _ _ _ _ w₁.2 w₂.2⟩
  end
end
