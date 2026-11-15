/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.Derangements.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

/-!
# Derangements on fintypes

This file contains lemmas that describe the cardinality of `derangements α` when `α` is a fintype.

## Main definitions

* `card_derangements_invariant`: A lemma stating that the number of derangements on a type `α`
    depends only on the cardinality of `α`.
* `numDerangements n`: The number of derangements on an n-element set, defined in a computation-
    friendly way.
* `card_derangements_eq_numDerangements`: Proof that `numDerangements` really does compute the
    number of derangements.
* `numDerangements_sum`: A lemma giving an expression for `numDerangements n` in terms of
    factorials.
-/

@[expose] public section


open derangements Equiv Fintype

variable {α : Type*} [DecidableEq α] [Fintype α]

instance : DecidablePred (· ∈ derangements α) := fun _ => Fintype.decidableForallFintype

instance : Fintype (derangements α) :=
  inferInstanceAs <| Fintype { f : Perm α | ∀ x : α, f x ≠ x }


theorem card_derangements_invariant {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (h : card α = card β) : card (derangements α) = card (derangements β) :=
  Fintype.card_congr (Equiv.derangementsCongr <| equivOfCardEq h)

theorem card_derangements_fin_add_two (n : ℕ) :
    card (derangements (Fin (n + 2))) =
      (n + 1) * card (derangements (Fin n)) + (n + 1) * card (derangements (Fin (n + 1))) := by sorry
def numDerangements : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (numDerangements n + numDerangements (n + 1))

@[simp]
theorem numDerangements_zero : numDerangements 0 = 1 :=
  rfl

@[simp]
theorem numDerangements_one : numDerangements 1 = 0 :=
  rfl

theorem numDerangements_add_two (n : ℕ) :
    numDerangements (n + 2) = (n + 1) * (numDerangements n + numDerangements (n + 1)) :=
  rfl

theorem numDerangements_succ (n : ℕ) :
    (numDerangements (n + 1) : ℤ) = (n + 1) * (numDerangements n : ℤ) - (-1) ^ n := by sorry
theorem card_derangements_fin_eq_numDerangements {n : ℕ} :
    card (derangements (Fin n)) = numDerangements n := by sorry
theorem card_derangements_eq_numDerangements (α : Type*) [Fintype α] [DecidableEq α] :
    card (derangements α) = numDerangements (card α) := by sorry
theorem numDerangements_sum (n : ℕ) :
    (numDerangements n : ℤ) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * Nat.ascFactorial (k + 1) (n - k) := by sorry
