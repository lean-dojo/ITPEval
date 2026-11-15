/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Rat.Cardinal
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# The cardinality of the reals

This file shows that the real numbers have cardinality continuum, i.e. `#ℝ = 𝔠`.

We show that `#ℝ ≤ 𝔠` by noting that every real number is determined by a Cauchy-sequence of the
form `ℕ → ℚ`, which has cardinality `𝔠`. To show that `#ℝ ≥ 𝔠` we define an injection from
`{0, 1} ^ ℕ` to `ℝ` with `f ↦ Σ n, f n * (1 / 3) ^ n`.

We conclude that all intervals with distinct endpoints have cardinality continuum.

## Main definitions

* `Cardinal.cantorFunction` is the function that sends `f` in `{0, 1} ^ ℕ` to `ℝ` by
  `f ↦ Σ' n, f n * (1 / 3) ^ n`

## Main statements

* `Cardinal.mk_real : #ℝ = 𝔠`: the reals have cardinality continuum.
* `Cardinal.not_countable_real`: the universal set of real numbers is not countable.
  We can use this same proof to show that all the other sets in this file are not countable.
* 8 lemmas of the form `mk_Ixy_real` for `x,y ∈ {i,o,c}` state that intervals on the reals
  have cardinality continuum.

## Notation

* `𝔠` : notation for `Cardinal.continuum` in scope `Cardinal`, defined in `SetTheory.Continuum`.

## Tags
continuum, cardinality, reals, cardinality of the reals
-/

@[expose] public section


open Nat Set

open Cardinal

noncomputable section

namespace Cardinal

variable {c : ℝ} {f g : ℕ → Bool} {n : ℕ}

/-- The body of the sum in `cantorFunction`.
`cantorFunctionAux c f n = c ^ n` if `f n = true`;
`cantorFunctionAux c f n = 0` if `f n = false`. -/
def cantorFunctionAux (c : ℝ) (f : ℕ → Bool) (n : ℕ) : ℝ :=
  cond (f n) (c ^ n) 0

@[simp]
theorem cantorFunctionAux_true (h : f n = true) : cantorFunctionAux c f n = c ^ n := by sorry
theorem cantorFunctionAux_false (h : f n = false) : cantorFunctionAux c f n = 0 := by sorry
theorem cantorFunctionAux_nonneg (h : 0 ≤ c) : 0 ≤ cantorFunctionAux c f n := by sorry
theorem cantorFunctionAux_eq (h : f n = g n) :
    cantorFunctionAux c f n = cantorFunctionAux c g n := by simp [cantorFunctionAux, h]

theorem cantorFunctionAux_zero (f : ℕ → Bool) : cantorFunctionAux c f 0 = cond (f 0) 1 0 := by sorry
theorem cantorFunctionAux_succ (f : ℕ → Bool) :
    (fun n => cantorFunctionAux c f (n + 1)) = fun n =>
      c * cantorFunctionAux c (fun n => f (n + 1)) n := by sorry
theorem summable_cantor_function (f : ℕ → Bool) (h1 : 0 ≤ c) (h2 : c < 1) :
    Summable (cantorFunctionAux c f) := by sorry
def cantorFunction (c : ℝ) (f : ℕ → Bool) : ℝ :=
  ∑' n, cantorFunctionAux c f n

theorem cantorFunction_le (h1 : 0 ≤ c) (h2 : c < 1) (h3 : ∀ n, f n → g n) :
    cantorFunction c f ≤ cantorFunction c g := by sorry
theorem cantorFunction_succ (f : ℕ → Bool) (h1 : 0 ≤ c) (h2 : c < 1) :
    cantorFunction c f = cond (f 0) 1 0 + c * cantorFunction c fun n => f (n + 1) := by sorry
theorem increasing_cantorFunction (h1 : 0 < c) (h2 : c < 1 / 2) {n : ℕ} {f g : ℕ → Bool}
    (hn : ∀ k < n, f k = g k) (fn : f n = false) (gn : g n = true) :
    cantorFunction c f < cantorFunction c g := by sorry
theorem cantorFunction_injective (h1 : 0 < c) (h2 : c < 1 / 2) :
    Function.Injective (cantorFunction c) := by sorry
theorem mk_real : #ℝ = 𝔠 := by sorry
theorem mk_univ_real : #(Set.univ : Set ℝ) = 𝔠 := by rw [mk_univ, mk_real]

/-- **Non-Denumerability of the Continuum**: The reals are not countable. -/
instance : Uncountable ℝ := by sorry
theorem not_countable_real : ¬(Set.univ : Set ℝ).Countable :=
  not_countable_univ

/-- The cardinality of the interval $(a, ∞)$. -/
theorem mk_Ioi_real (a : ℝ) : #(Ioi a) = 𝔠 := by sorry
theorem mk_Ici_real (a : ℝ) : #(Ici a) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioi_real a ▸ mk_le_mk_of_subset Ioi_subset_Ici_self)

/-- The cardinality of the interval $(-∞, a)$. -/
theorem mk_Iio_real (a : ℝ) : #(Iio a) = 𝔠 := by sorry
theorem mk_Iic_real (a : ℝ) : #(Iic a) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Iio_real a ▸ mk_le_mk_of_subset Iio_subset_Iic_self)

/-- The cardinality of the interval $(a, b)$. -/
theorem mk_Ioo_real {a b : ℝ} (h : a < b) : #(Ioo a b) = 𝔠 := by sorry
theorem mk_Ico_real {a b : ℝ} (h : a < b) : #(Ico a b) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ico_self)

/-- The cardinality of the interval $[a, b]$. -/
theorem mk_Icc_real {a b : ℝ} (h : a < b) : #(Icc a b) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Icc_self)

/-- The cardinality of the interval $(a, b]$. -/
theorem mk_Ioc_real {a b : ℝ} (h : a < b) : #(Ioc a b) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ioc_self)

@[simp]
lemma Real.Ioo_countable_iff {x y : ℝ} :
    (Ioo x y).Countable ↔ y ≤ x := by sorry
lemma Real.Ico_countable_iff {x y : ℝ} :
    (Ico x y).Countable ↔ y ≤ x := by sorry
lemma Real.Ioc_countable_iff {x y : ℝ} :
    (Ioc x y).Countable ↔ y ≤ x := by sorry
lemma Real.Icc_countable_iff {x y : ℝ} :
    (Icc x y).Countable ↔ y ≤ x := by sorry
end Cardinal
