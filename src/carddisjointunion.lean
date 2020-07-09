import tactic
import tactic.suggest
import tactic.nth_rewrite
import data.fintype.basic
import data.setoid.partition

variables {α : Type} {β : Type} {γ : Type}

open_locale classical
open_locale big_operators

lemma lift_disjoint_to_finset (s1 s2 : set α) [fintype α] (h : disjoint s1 s2) : disjoint s1.to_finset s2.to_finset :=
begin
    intros a hinter,
    have hset : a ∈ ∅,
    {
        rw ←set.bot_eq_empty,
        rw ←le_bot_iff.mp h,
        apply (set.mem_inter_iff a s1 s2).mpr ,
        split,
        exact set.mem_to_finset.mp (finset.mem_of_mem_inter_left hinter),
        exact set.mem_to_finset.mp (finset.mem_of_mem_inter_right hinter),
    },
    exfalso,
    apply set.not_mem_empty a hset,
end

lemma to_finset_bind_eq_univ_of_partition {c : set (set α)} [fintype α] (h : setoid.is_partition c) :
    (set.to_finset c).bind(λ (x : set α), x.to_finset) = finset.univ :=
begin
    ext,
    split,
    {
        simp,
    },
    {
        intro ha,
        rw finset.mem_bind,
        cases h.2 a with s hs,
        simp at hs,
        use s,
        rcases hs with ⟨⟨hmemsc, hmemas⟩, _⟩,
        split,
        {
            exact set.mem_to_finset.mpr hmemsc,
        },
        {
            exact set.mem_to_finset.mpr hmemas,
        }
    }
end

lemma sum_card_partition {c : set (set α)} [fintype α] (h : setoid.is_partition c):
    fintype.card α = (set.to_finset c).sum(λ x, (set.to_finset x).card) := begin
    /- proof idea: |α| = Σ x in α, 1 = Σ x in (⋃ s in c, s), 1
                       = Σ s in c, (Σ x in s, 1)
                       = Σ s in c, |s|  -/
    conv
    begin
        to_rhs,
        congr,
        skip,
        funext,
        rw finset.card_eq_sum_ones,
    end,
    have hdisjoint : ∀ (x : set α), x ∈ c.to_finset → ∀ (y : set α), y ∈ c.to_finset → x ≠ y → disjoint x.to_finset y.to_finset,
    {
        intros x hx y hy hne,
        apply lift_disjoint_to_finset,
        exact setoid.is_partition.pairwise_disjoint h x (set.mem_to_finset.mp hx) y (set.mem_to_finset.mp hy) hne,
    },
    rw ← finset.sum_bind hdisjoint,
    rw ←finset.card_eq_sum_ones,
    rw to_finset_bind_eq_univ_of_partition h,
    exact finset.card_univ.symm,
end

