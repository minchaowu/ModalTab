import .ops
open subtype nnf tmodel list

def unmodal_seqt (Γ : sseqt) : list sseqt :=
@list.pmap _ _ (λ φ, φ ∉ Γ.h ∧ dia φ ∈ Γ.m)
(λ d h,
({goal := Γ.goal,
s := some {d := d, b := Γ.b},
a := {d := d, b := Γ.b} :: Γ.a,
h := d :: Γ.h,
b := Γ.b,
m := d :: Γ.b,
ndh := begin rw list.nodup_cons, split, exact h.1, exact Γ.ndh end,
ndb := Γ.ndb,
sph := begin apply list.cons_subperm_of_mem, apply Γ.ndh, exact h.1, apply mem_closure_dia, apply Γ.sbm, exact h.2,  exact Γ.sph end,
spb := Γ.spb,
sbm := begin rw list.cons_subset, split, apply mem_closure_dia, apply Γ.sbm, exact h.2, apply list.subset_of_subperm, exact Γ.spb end
} : sseqt))
(filter_undia Γ.h Γ.m)
(begin
intros φ hmem,
split, 
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
