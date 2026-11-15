/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Monotone
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős–Szekeres theorem

This file proves Theorem 73 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/), also
known as the Erdős–Szekeres theorem: given a sequence of more than `r * s` distinct
values, there is an increasing sequence of length longer than `r` or a decreasing sequence of length
longer than `s`.

We use the proof outlined at
https://en.wikipedia.org/wiki/Erdos-Szekeres_theorem#Pigeonhole_principle.

## Tags

sequences, increasing, decreasing, Ramsey, Erdos-Szekeres, Erdős–Szekeres, Erdős-Szekeres
-/

open Function Finset

namespace Theorems100

variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β] {f : α → β} {i : α}

/-- The possible lengths of an increasing sequence which ends at `i`. -/
private noncomputable def incSequencesTo (f : α → β) (i : α) : Finset ℕ :=
  open Classical in
  image card {t : Finset α | IsGreatest t i ∧ StrictMonoOn f t}

/-- The possible lengths of a decreasing sequence which ends at `i`. -/
private noncomputable def decSequencesTo (f : α → β) (i : α) : Finset ℕ :=
  open Classical in
  image card {t : Finset α | IsGreatest t i ∧ StrictAntiOn f t}

/-- The singleton sequence is increasing, so 1 is a possible length. -/
private lemma one_mem_incSequencesTo : 1 ∈ incSequencesTo f i := mem_image.2 ⟨{i}, by simp⟩
/-- The singleton sequence is decreasing, so 1 is a possible length. -/
private lemma one_mem_decSequencesTo : 1 ∈ decSequencesTo f i := one_mem_incSequencesTo (β := βᵒᵈ)

/-- The singleton sequence is increasing, so the set of lengths is nonempty. -/
private lemma incSequencesTo_nonempty : (incSequencesTo f i).Nonempty := ⟨1, one_mem_incSequencesTo⟩
/-- The singleton sequence is decreasing, so the set of lengths is nonempty. -/
private lemma decSequencesTo_nonempty : (decSequencesTo f i).Nonempty := ⟨1, one_mem_decSequencesTo⟩

/-- The maximum length of an increasing sequence which ends at `i`. -/
private noncomputable def maxIncSequencesTo (f : α → β) (i : α) : ℕ :=
  max' (incSequencesTo f i) incSequencesTo_nonempty

/-- The maximum length of a decreasing sequence which ends at `i`. -/
private noncomputable def maxDecSequencesTo (f : α → β) (i : α) : ℕ :=
  max' (decSequencesTo f i) decSequencesTo_nonempty

private lemma one_le_maxIncSequencesTo : 1 ≤ maxIncSequencesTo f i :=
  le_max' _ _ one_mem_incSequencesTo
private lemma one_le_maxDecSequencesTo : 1 ≤ maxDecSequencesTo f i :=
  le_max' _ _ one_mem_decSequencesTo

private lemma maxIncSequencesTo_mem : maxIncSequencesTo f i ∈ incSequencesTo f i :=
  max'_mem _ incSequencesTo_nonempty
private lemma maxDecSequencesTo_mem : maxDecSequencesTo f i ∈ decSequencesTo f i :=
  max'_mem _ decSequencesTo_nonempty

/--
We will want to show that if `i ≠ j`, then the pairs
`(maxIncSequencesTo f i, maxDecSequencesTo f i)` and
`(maxIncSequencesTo f j, maxDecSequencesTo f j)` are different.
To this end, we will assume wlog that `i < j`, and show that if `f i < f j`,
then `maxIncSequencesTo f i < maxIncSequencesTo f j`, and later dualise to prove that if `f j < f i`
then `maxDecSequencesTo f i < maxDecSequencesTo f j`.
-/
private lemma maxIncSequencesTo_lt {i j : α} (hij : i < j) (hfij : f i < f j) :
    maxIncSequencesTo f i < maxIncSequencesTo f j := by sorry
theorem erdos_szekeres {r s : ℕ} {f : α → β} (hn : r * s < Fintype.card α) (hf : Injective f) :
    (∃ t : Finset α, r < #t ∧ StrictMonoOn f t) ∨
      ∃ t : Finset α, s < #t ∧ StrictAntiOn f t := by sorry
end Theorems100
