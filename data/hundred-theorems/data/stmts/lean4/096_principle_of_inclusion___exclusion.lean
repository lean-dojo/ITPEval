/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.BigOperators

/-!
# Inclusion-exclusion principle

This file proves several variants of the inclusion-exclusion principle.

The inclusion-exclusion principle says that the sum/integral of a function over a finite union of
sets can be calculated as the alternating sum over `n > 0` of the sum/integral of the function over
the intersection of `n` of the sets.

By taking complements, it also says that the sum/integral of a function over a finite intersection
of complements of sets can be calculated as the alternating sum over `n ≥ 0` of the sum/integral of
the function over the intersection of `n` of the sets.

By taking the function to be constant `1`, we instead get a result about the cardinality/measure of
the sets.

## Main declarations

Per the above explanation, this file contains the following variants of inclusion-exclusion:
* `Finset.inclusion_exclusion_sum_biUnion`: Sum of a function over a finite union of sets
* `Finset.inclusion_exclusion_card_biUnion`: Cardinality of a finite union of sets
* `Finset.inclusion_exclusion_sum_inf_compl`: Sum of a function over a finite intersection of
  complements of sets
* `Finset.inclusion_exclusion_card_inf_compl`: Cardinality of a finite intersection of
  complements of sets

See also `MeasureTheory.integral_biUnion_eq_sum_powerset` for the version with integrals, and
`MeasureTheory.measureReal_biUnion_eq_sum_powerset` for the version with measures.

## TODO

* Prove that truncating the series alternatively gives an upper/lower bound to the true value.
-/

public section

assert_not_exists Field

namespace Finset
variable {ι α G : Type*} [AddCommGroup G] {s : Finset ι}

lemma prod_indicator_biUnion_sub_indicator (hs : s.Nonempty) (S : ι → Set α) (a : α) :
    ∏ i ∈ s, (Set.indicator (⋃ i ∈ s, S i) 1 a - Set.indicator (S i) 1 a) = (0 : ℤ) := by sorry
lemma indicator_biUnion_eq_sum_powerset (s : Finset ι) (S : ι → Set α) (f : α → G) (a : α) :
    Set.indicator (⋃ i ∈ s, S i) f a = ∑ t ∈ s.powerset with t.Nonempty,
      (-1) ^ (#t + 1) • Set.indicator (⋂ i ∈ t, S i) f a := by sorry
variable [DecidableEq α]

lemma prod_indicator_biUnion_finset_sub_indicator (hs : s.Nonempty) (S : ι → Finset α) (a : α) :
    ∏ i ∈ s, (Set.indicator (s.biUnion S) 1 a - Set.indicator (S i) 1 a) = (0 : ℤ) := by sorry
theorem inclusion_exclusion_sum_biUnion (s : Finset ι) (S : ι → Finset α) (f : α → G) :
    ∑ a ∈ s.biUnion S, f a = ∑ t : s.powerset.filter (·.Nonempty),
      (-1) ^ (#t.1 + 1) • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 S, f a := by sorry
theorem inclusion_exclusion_card_biUnion (s : Finset ι) (S : ι → Finset α) :
    #(s.biUnion S) = ∑ t : s.powerset.filter (·.Nonempty),
      (-1 : ℤ) ^ (#t.1 + 1) * #(t.1.inf' (mem_filter.1 t.2).2 S) := by sorry
variable [Fintype α]

/-- **Inclusion-exclusion principle** for the sum of a function over an intersection of complements.

The sum of a function `f` over the intersection of the complements of the `S i` over `i ∈ s` is the
alternating sum of the sums of `f` over the intersections of the `S i`. -/
theorem inclusion_exclusion_sum_inf_compl (s : Finset ι) (S : ι → Finset α) (f : α → G) :
    ∑ a ∈ s.inf fun i ↦ (S i)ᶜ, f a = ∑ t ∈ s.powerset, (-1) ^ #t • ∑ a ∈ t.inf S, f a := by sorry
theorem inclusion_exclusion_card_inf_compl (s : Finset ι) (S : ι → Finset α) :
    #(s.inf fun i ↦ (S i)ᶜ) = ∑ t ∈ s.powerset, (-1 : ℤ) ^ #t * #(t.inf S) := by sorry
end Finset
