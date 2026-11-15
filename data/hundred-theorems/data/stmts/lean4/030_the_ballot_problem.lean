/-
Copyright (c) 2022 Bhavik Mehta, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kexing Ying
-/
import Mathlib.Probability.UniformOn

/-!
# Ballot problem

This file proves Theorem 30 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The ballot problem asks, if in an election, candidate A receives `p` votes whereas candidate B
receives `q` votes where `p > q`, what is the probability that candidate A is strictly ahead
throughout the count. The probability of this is `(p - q) / (p + q)`.

## Main definitions

* `countedSequence`: given natural numbers `p` and `q`, `countedSequence p q` is the set of
  all lists containing `p` of `1`s and `q` of `-1`s representing the votes of candidate A and B
  respectively.
* `staysPositive`: is the set of lists of integers which suffix has positive sum. In particular,
  the intersection of this set with `countedSequence` is the set of lists where candidate A is
  strictly ahead.

## Main result

* `ballot_problem`: the ballot problem.

-/


open Set ProbabilityTheory MeasureTheory
open scoped ENNReal

namespace Ballot

/-- The set of nonempty lists of integers which suffix has positive sum. -/
def staysPositive : Set (List ℤ) :=
  {l | ∀ l₂, l₂ ≠ [] → l₂ <:+ l → 0 < l₂.sum}

@[simp]
theorem staysPositive_nil : [] ∈ staysPositive :=
  fun _ hl hl₁ => (hl (List.eq_nil_of_suffix_nil hl₁)).elim

theorem staysPositive_suffix {l₁ l₂ : List ℤ} (hl₂ : l₂ ∈ staysPositive) (h : l₁ <:+ l₂) :
    l₁ ∈ staysPositive := fun l hne hl ↦ hl₂ l hne <| hl.trans h

theorem staysPositive_cons {x : ℤ} {l : List ℤ} :
    x::l ∈ staysPositive ↔ l ∈ staysPositive ∧ 0 < x + l.sum := by sorry
theorem sum_nonneg_of_staysPositive : ∀ {l : List ℤ}, l ∈ staysPositive → 0 ≤ l.sum := by sorry
theorem staysPositive_cons_pos (x : ℤ) (hx : 0 < x) (l : List ℤ) :
    (x::l) ∈ staysPositive ↔ l ∈ staysPositive := by sorry
def countedSequence (p q : ℕ) : Set (List ℤ) :=
  {l | l.count 1 = p ∧ l.count (-1) = q ∧ ∀ x ∈ l, x = (1 : ℤ) ∨ x = -1}

open scoped List in
/-- An alternative definition of `countedSequence` that uses `List.Perm`. -/
theorem mem_countedSequence_iff_perm {p q l} :
    l ∈ countedSequence p q ↔ l ~ List.replicate p (1 : ℤ) ++ List.replicate q (-1) := by sorry
theorem counted_right_zero (p : ℕ) : countedSequence p 0 = {List.replicate p 1} := by sorry
theorem counted_left_zero (q : ℕ) : countedSequence 0 q = {List.replicate q (-1)} := by sorry
theorem mem_of_mem_countedSequence {p q} {l} (hl : l ∈ countedSequence p q) {x : ℤ} (hx : x ∈ l) :
    x = 1 ∨ x = -1 :=
  hl.2.2 x hx

theorem length_of_mem_countedSequence {p q} {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l.length = p + q := by simp [(mem_countedSequence_iff_perm.1 hl).length_eq]

theorem counted_eq_nil_iff {p q : ℕ} {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l = [] ↔ p = 0 ∧ q = 0 :=
  List.length_eq_zero_iff.symm.trans <| by simp [length_of_mem_countedSequence hl]

theorem counted_ne_nil_left {p q : ℕ} (hp : p ≠ 0) {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l ≠ [] := by simp [counted_eq_nil_iff hl, hp]

theorem counted_ne_nil_right {p q : ℕ} (hq : q ≠ 0) {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l ≠ [] := by simp [counted_eq_nil_iff hl, hq]

theorem counted_succ_succ (p q : ℕ) :
    countedSequence (p + 1) (q + 1) =
      List.cons 1 '' countedSequence p (q + 1) ∪ List.cons (-1) '' countedSequence (p + 1) q := by sorry
theorem countedSequence_finite : ∀ p q : ℕ, (countedSequence p q).Finite := by sorry
theorem countedSequence_nonempty : ∀ p q : ℕ, (countedSequence p q).Nonempty := by sorry
theorem sum_of_mem_countedSequence {p q} {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l.sum = p - q := by simp [(mem_countedSequence_iff_perm.1 hl).sum_eq, sub_eq_add_neg]

theorem disjoint_bits (p q : ℕ) :
    Disjoint (List.cons 1 '' countedSequence p (q + 1))
      (List.cons (-1) '' countedSequence (p + 1) q) := by sorry
open MeasureTheory.Measure

private local instance measurableSpace_list_int : MeasurableSpace (List ℤ) := ⊤

private local instance measurableSingletonClass_list_int : MeasurableSingletonClass (List ℤ) :=
  { measurableSet_singleton := fun _ => trivial }

private theorem list_int_measurableSet {s : Set (List ℤ)} : MeasurableSet s := trivial

theorem count_countedSequence : ∀ p q : ℕ, count (countedSequence p q) = (p + q).choose p := by sorry
theorem first_vote_pos :
    ∀ p q,
      0 < p + q → uniformOn (countedSequence p q : Set (List ℤ)) {l | l.headI = 1} = p / (p + q) := by sorry
theorem headI_mem_of_nonempty {α : Type*} [Inhabited α] : ∀ {l : List α} (_ : l ≠ []), l.headI ∈ l := by sorry
theorem first_vote_neg (p q : ℕ) (h : 0 < p + q) :
    uniformOn (countedSequence p q) {l | l.headI = 1}ᶜ = q / (p + q) := by sorry
theorem ballot_same (p : ℕ) : uniformOn (countedSequence (p + 1) (p + 1)) staysPositive = 0 := by sorry
theorem ballot_edge (p : ℕ) : uniformOn (countedSequence (p + 1) 0) staysPositive = 1 := by sorry
theorem countedSequence_int_pos_counted_succ_succ (p q : ℕ) :
    countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1} =
      (countedSequence p (q + 1)).image (List.cons 1) := by sorry
theorem ballot_pos (p q : ℕ) :
    uniformOn (countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}) staysPositive =
      uniformOn (countedSequence p (q + 1)) staysPositive := by sorry
theorem countedSequence_int_neg_counted_succ_succ (p q : ℕ) :
    countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}ᶜ =
      (countedSequence (p + 1) q).image (List.cons (-1)) := by sorry
theorem ballot_neg (p q : ℕ) (qp : q < p) :
    uniformOn (countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}ᶜ) staysPositive =
      uniformOn (countedSequence (p + 1) q) staysPositive := by sorry
theorem ballot_problem' :
    ∀ q p, q < p → (uniformOn (countedSequence p q) staysPositive).toReal = (p - q) / (p + q) := by sorry
theorem ballot_problem :
    ∀ q p, q < p → uniformOn (countedSequence p q) staysPositive = (p - q) / (p + q) := by sorry
end Ballot
