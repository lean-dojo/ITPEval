/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne, Jireh Loreaux
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Real.ConjExponents

/-!
# Mean value inequalities

In this file we prove several inequalities for finite sums, including AM-GM inequality,
HM-GM inequality, Young's inequality, Hölder inequality, and Minkowski inequality. Versions for
integrals of some of these inequalities are available in
`Mathlib/MeasureTheory/Integral/MeanInequalities.lean`.

## Main theorems

### AM-GM inequality:

The inequality says that the geometric mean of a tuple of non-negative numbers is less than or equal
to their arithmetic mean. We prove the weighted version of this inequality: if $w$ and $z$
are two non-negative vectors and $\sum_{i\in s} w_i=1$, then
$$
\prod_{i\in s} z_i^{w_i} ≤ \sum_{i\in s} w_iz_i.
$$
The classical version is a special case of this inequality for $w_i=\frac{1}{n}$.

We prove a few versions of this inequality. Each of the following lemmas comes in two versions:
a version for real-valued non-negative functions is in the `Real` namespace, and a version for
`NNReal`-valued functions is in the `NNReal` namespace.

- `geom_mean_le_arith_mean_weighted` : weighted version for functions on `Finset`s;
- `geom_mean_le_arith_mean2_weighted` : weighted version for two numbers;
- `geom_mean_le_arith_mean3_weighted` : weighted version for three numbers;
- `geom_mean_le_arith_mean4_weighted` : weighted version for four numbers.


### HM-GM inequality:

The inequality says that the harmonic mean of a tuple of positive numbers is less than or equal
to their geometric mean. We prove the weighted version of this inequality: if $w$ and $z$
are two positive vectors and $\sum_{i\in s} w_i=1$, then
$$
1/(\sum_{i\in s} w_i/z_i) ≤ \prod_{i\in s} z_i^{w_i}
$$
The classical version is proven as a special case of this inequality for $w_i=\frac{1}{n}$.

The inequalities are proven only for real-valued positive functions on `Finset`s, and namespaced in
`Real`. The weighted version follows as a corollary of the weighted AM-GM inequality.

### Young's inequality

Young's inequality says that for non-negative numbers `a`, `b`, `p`, `q` such that
$\frac{1}{p}+\frac{1}{q}=1$ we have
$$
ab ≤ \frac{a^p}{p} + \frac{b^q}{q}.
$$

This inequality is a special case of the AM-GM inequality. It is then used to prove Hölder's
inequality (see below).

### Hölder's inequality

The inequality says that for two conjugate exponents `p` and `q` (i.e., for two positive numbers
such that $\frac{1}{p}+\frac{1}{q}=1$) and any two non-negative vectors their inner product is
less than or equal to the product of the $L_p$ norm of the first vector and the $L_q$ norm of the
second vector:
$$
\sum_{i\in s} a_ib_i ≤ \sqrt[p]{\sum_{i\in s} a_i^p}\sqrt[q]{\sum_{i\in s} b_i^q}.
$$

We give versions of this result in `ℝ`, `ℝ≥0` and `ℝ≥0∞`.

There are at least two short proofs of this inequality. In our proof we prenormalize both vectors,
then apply Young's inequality to each $a_ib_i$. Another possible proof would be to deduce this
inequality from the generalized mean inequality for well-chosen vectors and weights.

### Minkowski's inequality

The inequality says that for `p ≥ 1` the function
$$
\|a\|_p=\sqrt[p]{\sum_{i\in s} a_i^p}
$$
satisfies the triangle inequality $\|a+b\|_p\le \|a\|_p+\|b\|_p$.

We give versions of this result in `Real`, `ℝ≥0` and `ℝ≥0∞`.

We deduce this inequality from Hölder's inequality. Namely, Hölder inequality implies that $\|a\|_p$
is the maximum of the inner product $\sum_{i\in s}a_ib_i$ over `b` such that $\|b\|_q\le 1$. Now
Minkowski's inequality follows from the fact that the maximum value of the sum of two functions is
less than or equal to the sum of the maximum values of the summands.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `StrictConvexOn` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.

-/

public section


universe u v

open Finset NNReal ENNReal
open scoped BigOperators

noncomputable section

variable {ι : Type u} (s : Finset ι)

section GeomMeanLEArithMean

/-! ### AM-GM inequality -/


namespace Real

/-- **AM-GM inequality**: The geometric mean is less than or equal to the arithmetic mean, weighted
version for real-valued nonnegative functions. -/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i := by sorry
theorem geom_mean_le_arith_mean {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : 0 < ∑ i ∈ s, w i) (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∏ i ∈ s, z i ^ w i) ^ (∑ i ∈ s, w i)⁻¹ ≤ (∑ i ∈ s, w i * z i) / (∑ i ∈ s, w i) := by sorry
theorem geom_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (hx : ∀ i ∈ s, w i ≠ 0 → z i = x) :
    ∏ i ∈ s, z i ^ w i = x :=
  calc
    ∏ i ∈ s, z i ^ w i = ∏ i ∈ s, x ^ w i := by sorry
theorem arith_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw' : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, w i ≠ 0 → z i = x) : ∑ i ∈ s, w i * z i = x :=
  calc
    ∑ i ∈ s, w i * z i = ∑ i ∈ s, w i * x := by sorry
theorem geom_mean_eq_arith_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (hx : ∀ i ∈ s, w i ≠ 0 → z i = x) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i := by sorry
theorem geom_mean_eq_arith_mean_weighted_iff' (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i ↔ ∀ j ∈ s, z j = ∑ i ∈ s, w i * z i := by sorry
theorem geom_mean_eq_arith_mean_weighted_iff (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i ↔ ∀ j ∈ s, w j ≠ 0 → z j = ∑ i ∈ s, w i * z i := by sorry
theorem geom_mean_lt_arith_mean_weighted_iff_of_pos (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i < ∑ i ∈ s, w i * z i ↔ ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k := by sorry
end Real

namespace NNReal

/-- **AM-GM inequality**: The geometric mean is less than or equal to the arithmetic mean, weighted
version for `NNReal`-valued functions. -/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ≥0) (hw' : ∑ i ∈ s, w i = 1) :
    (∏ i ∈ s, z i ^ (w i : ℝ)) ≤ ∑ i ∈ s, w i * z i :=
  mod_cast
    Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => (w i).coe_nonneg)
      (by assumption_mod_cast) fun i _ => (z i).coe_nonneg

/-- **AM-GM inequality**: The geometric mean is less than or equal to the arithmetic mean, weighted
version for two `NNReal` numbers. -/
theorem geom_mean_le_arith_mean2_weighted (w₁ w₂ p₁ p₂ : ℝ≥0) :
    w₁ + w₂ = 1 → p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) ≤ w₁ * p₁ + w₂ * p₂ := by sorry
theorem geom_mean_le_arith_mean3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ : ℝ≥0) :
    w₁ + w₂ + w₃ = 1 →
      p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) * p₃ ^ (w₃ : ℝ) ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ := by sorry
theorem geom_mean_le_arith_mean4_weighted (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ≥0) :
    w₁ + w₂ + w₃ + w₄ = 1 →
      p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) * p₃ ^ (w₃ : ℝ) * p₄ ^ (w₄ : ℝ) ≤
        w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ := by sorry
end NNReal

namespace Real

theorem geom_mean_le_arith_mean2_weighted {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) : p₁ ^ w₁ * p₂ ^ w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
  NNReal.geom_mean_le_arith_mean2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ <|
    NNReal.coe_inj.1 <| by assumption

theorem geom_mean_le_arith_mean3_weighted {w₁ w₂ w₃ p₁ p₂ p₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw₃ : 0 ≤ w₃) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) (hw : w₁ + w₂ + w₃ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ :=
  NNReal.geom_mean_le_arith_mean3_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
      ⟨p₃, hp₃⟩ <|
    NNReal.coe_inj.1 hw

theorem geom_mean_le_arith_mean4_weighted {w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ} (hw₁ : 0 ≤ w₁)
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hw₄ : 0 ≤ w₄) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hp₄ : 0 ≤ p₄) (hw : w₁ + w₂ + w₃ + w₄ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ * p₄ ^ w₄ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
  NNReal.geom_mean_le_arith_mean4_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨w₄, hw₄⟩ ⟨p₁, hp₁⟩
      ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ ⟨p₄, hp₄⟩ <|
    NNReal.coe_inj.1 <| by assumption

end Real

end GeomMeanLEArithMean

section HarmMeanLEGeomMean

/-! ### HM-GM inequality -/

namespace Real

/-- **HM-GM inequality**: The harmonic mean is less than or equal to the geometric mean, weighted
version for real-valued nonnegative functions. -/
theorem harm_mean_le_geom_mean_weighted (w z : ι → ℝ) (hs : s.Nonempty) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) :
    (∑ i ∈ s, w i / z i)⁻¹ ≤ ∏ i ∈ s, z i ^ w i := by sorry
theorem harm_mean_le_geom_mean {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) (hw' : 0 < ∑ i ∈ s, w i) (hz : ∀ i ∈ s, 0 < z i) :
    (∑ i ∈ s, w i) / (∑ i ∈ s, w i / z i) ≤ (∏ i ∈ s, z i ^ w i) ^ (∑ i ∈ s, w i)⁻¹ := by sorry
end Real

end HarmMeanLEGeomMean


section Young

/-! ### Young's inequality -/


namespace Real

/-- **Young's inequality**, a version for nonnegative real numbers. -/
theorem young_inequality_of_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpq : p.HolderConjugate q) : a * b ≤ a ^ p / p + b ^ q / q := by sorry
theorem young_inequality (a b : ℝ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ |a| ^ p / p + |b| ^ q / q :=
  calc
    a * b ≤ |a * b| := le_abs_self (a * b)
    _ = |a| * |b| := abs_mul a b
    _ ≤ |a| ^ p / p + |b| ^ q / q :=
      Real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq

end Real

namespace NNReal

/-- **Young's inequality**, `ℝ≥0` version. We use `{p q : ℝ≥0}` in order to avoid constructing
witnesses of `0 ≤ p` and `0 ≤ q` for the denominators. -/
theorem young_inequality (a b : ℝ≥0) {p q : ℝ≥0} (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ (p : ℝ) / p + b ^ (q : ℝ) / q :=
  Real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg hpq.coe

/-- **Young's inequality**, `ℝ≥0` version with real conjugate exponents. -/
theorem young_inequality_real (a b : ℝ≥0) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ p / Real.toNNReal p + b ^ q / Real.toNNReal q := by sorry
end NNReal

namespace ENNReal

/-- **Young's inequality**, `ℝ≥0∞` version with real conjugate exponents. -/
theorem young_inequality (a b : ℝ≥0∞) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ p / ENNReal.ofReal p + b ^ q / ENNReal.ofReal q := by sorry
end ENNReal

end Young

section HoelderMinkowski

/-! ### Hölder's and Minkowski's inequalities -/


namespace NNReal

private theorem inner_le_Lp_mul_Lp_of_norm_le_one (f g : ι → ℝ≥0) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : ∑ i ∈ s, f i ^ p ≤ 1) (hg : ∑ i ∈ s, g i ^ q ≤ 1) :
    ∑ i ∈ s, f i * g i ≤ 1 := by sorry
theorem inner_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by sorry
theorem Lr_rpow_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q r : ℝ} (hpqr : p.HolderTriple q r) :
    ∑ i ∈ s, (f i * g i) ^ r ≤ (∑ i ∈ s, f i ^ p) ^ (r / p) * (∑ i ∈ s, g i ^ q) ^ (r / q) := by sorry
theorem Lr_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q r : ℝ} (hpqr : p.HolderTriple q r) :
    (∑ i ∈ s, (f i * g i) ^ r) ^ (1 / r) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by sorry
lemma inner_le_weight_mul_Lp (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) (w f : ι → ℝ≥0) :
    ∑ i ∈ s, w i * f i ≤ (∑ i ∈ s, w i) ^ (1 - p⁻¹) * (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ := by sorry
theorem summable_and_Lr_rpow_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q r : ℝ}
    (hpqr : p.HolderTriple q r) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (Summable fun i => (f i * g i) ^ r) ∧
      ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by sorry
theorem summable_and_inner_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (Summable fun i => f i * g i) ∧
      ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by sorry
theorem summable_mul_rpow_of_Lp_Lq {f g : ι → ℝ≥0} {p q r : ℝ} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    Summable fun i => (f i * g i) ^ r :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).1

theorem summable_mul_of_Lp_Lq {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    Summable fun i => f i * g i :=
  (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).1

theorem Lr_rpow_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q r : ℝ} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).2

theorem Lr_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q r : ℝ} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (∑' i, (f i * g i) ^ r) ^ (1 / r) ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by sorry
theorem inner_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) :=
  (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).2

@[deprecated (since := "2026-02-12")] alias inner_le_Lp_mul_Lq_tsum' := inner_le_Lp_mul_Lq_tsum

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `NNReal`-valued
functions. For an alternative version, convenient if the infinite sums are not already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_tsum`. -/
theorem inner_le_Lp_mul_Lq_hasSum {f g : ι → ℝ≥0} {A B : ℝ≥0} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : HasSum (fun i => f i ^ p) (A ^ p))
    (hg : HasSum (fun i => g i ^ q) (B ^ q)) : ∃ C, C ≤ A * B ∧ HasSum (fun i => f i * g i) C := by sorry
theorem rpow_sum_le_const_mul_sum_rpow (f : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, f i) ^ p ≤ (#s : ℝ≥0) ^ (p - 1) * ∑ i ∈ s, f i ^ p := by sorry
theorem isGreatest_Lp (f : ι → ℝ≥0) {p q : ℝ} (hpq : p.HolderConjugate q) :
    IsGreatest ((fun g : ι → ℝ≥0 => ∑ i ∈ s, f i * g i) '' { g | ∑ i ∈ s, g i ^ q ≤ 1 })
      ((∑ i ∈ s, f i ^ p) ^ (1 / p)) := by sorry
theorem Lp_add_le (f g : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) + (∑ i ∈ s, g i ^ p) ^ (1 / p) := by sorry
theorem Lp_add_le_tsum {f g : ι → ℝ≥0} {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) :
    (Summable fun i => (f i + g i) ^ p) ∧
      (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤
        (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) := by sorry
theorem summable_Lp_add {f g : ι → ℝ≥0} {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) : Summable fun i => (f i + g i) ^ p :=
  (Lp_add_le_tsum hp hf hg).1

theorem Lp_add_le_tsum' {f g : ι → ℝ≥0} {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  (Lp_add_le_tsum hp hf hg).2

/-- **Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `NNReal`-valued functions. For an alternative version, convenient if the
infinite sums are not already expressed as `p`-th powers, see `Lp_add_le_tsum_of_nonneg`. -/
theorem Lp_add_le_hasSum {f g : ι → ℝ≥0} {A B : ℝ≥0} {p : ℝ} (hp : 1 ≤ p)
    (hf : HasSum (fun i => f i ^ p) (A ^ p)) (hg : HasSum (fun i => g i ^ p) (B ^ p)) :
    ∃ C, C ≤ A + B ∧ HasSum (fun i => (f i + g i) ^ p) (C ^ p) := by sorry
end NNReal

namespace Real

variable (f g : ι → ℝ) {p q r : ℝ}

/-- **Hölder inequality**: the sum of (the `r`-powers of) the product of two functions is bounded by
the product of their `L^p` and `L^q` norms when `p`, `q` and `r` form a `Real.HolderTriple`.
Version for sums over finite sets, with real-valued functions. -/
theorem Lr_rpow_le_Lp_mul_Lq (hpqr : HolderTriple p q r) :
    ∑ i ∈ s, |f i * g i| ^ r ≤ (∑ i ∈ s, |f i| ^ p) ^ (r / p) * (∑ i ∈ s, |g i| ^ q) ^ (r / q) := by sorry
theorem inner_le_Lp_mul_Lq (hpq : HolderConjugate p q) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, |f i| ^ p) ^ (1 / p) * (∑ i ∈ s, |g i| ^ q) ^ (1 / q) := by sorry
theorem rpow_sum_le_const_mul_sum_rpow (hp : 1 ≤ p) :
    (∑ i ∈ s, |f i|) ^ p ≤ (#s : ℝ) ^ (p - 1) * ∑ i ∈ s, |f i| ^ p := by sorry
theorem Lp_add_le (hp : 1 ≤ p) :
    (∑ i ∈ s, |f i + g i| ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, |f i| ^ p) ^ (1 / p) + (∑ i ∈ s, |g i| ^ p) ^ (1 / p) := by sorry
variable {f g}

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued nonnegative functions. -/
theorem inner_le_Lp_mul_Lq_of_nonneg (hpq : HolderConjugate p q) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by sorry
theorem Lr_rpow_le_Lp_mul_Lq_of_nonneg {ι : Type*} (s : Finset ι) {f g : ι → ℝ} {p q r : ℝ}
    (hpqr : p.HolderTriple q r) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, (f i * g i) ^ r ≤ (∑ i ∈ s, f i ^ p) ^ (r / p) * (∑ i ∈ s, g i ^ q) ^ (r / q) := by sorry
lemma inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s, w i * f i ≤ (∑ i ∈ s, w i) ^ (1 - p⁻¹) * (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ := by sorry
lemma compact_inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) {w f : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    𝔼 i ∈ s, w i * f i ≤ (𝔼 i ∈ s, w i) ^ (1 - p⁻¹) * (𝔼 i ∈ s, w i * f i ^ p) ^ p⁻¹ := by sorry
theorem summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p)
    (hg_sum : Summable fun i => g i ^ q) :
    (Summable fun i => (f i * g i) ^ r) ∧
      ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by sorry
theorem summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.HolderConjugate q)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p)
    (hg_sum : Summable fun i => g i ^ q) :
    (Summable fun i => f i * g i) ∧
      ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by sorry
theorem summable_Lr_of_Lp_Lq_of_nonneg (hpqr : p.HolderTriple q r) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    Summable fun i => (f i * g i) ^ r :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum).1

theorem summable_mul_of_Lp_Lq_of_nonneg (hpq : p.HolderConjugate q) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    Summable fun i => f i * g i :=
  (summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).1

theorem Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum).2

theorem Lr_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    (∑' i, (f i * g i) ^ r) ^ (1 / r) ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by sorry
theorem inner_le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.HolderConjugate q) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) :=
  (summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).2

@[deprecated (since := "2026-02-12")]
alias inner_le_Lp_mul_Lq_of_nonneg' := inner_le_Lp_mul_Lq_of_nonneg

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `NNReal`-valued
functions. For an alternative version, convenient if the infinite sums are not already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_tsum_of_nonneg`. -/
theorem inner_le_Lp_mul_Lq_hasSum_of_nonneg (hpq : p.HolderConjugate q) {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : HasSum (fun i => f i ^ p) (A ^ p)) (hg_sum : HasSum (fun i => g i ^ q) (B ^ q)) :
    ∃ C : ℝ, 0 ≤ C ∧ C ≤ A * B ∧ HasSum (fun i => f i * g i) C := by sorry
theorem rpow_sum_le_const_mul_sum_rpow_of_nonneg (hp : 1 ≤ p) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) ^ p ≤ (#s : ℝ) ^ (p - 1) * ∑ i ∈ s, f i ^ p := by sorry
theorem Lp_add_le_of_nonneg (hp : 1 ≤ p) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ i ∈ s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) + (∑ i ∈ s, g i ^ p) ^ (1 / p) := by sorry
theorem Lp_add_le_tsum_of_nonneg (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    (Summable fun i => (f i + g i) ^ p) ∧
      (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤
        (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) := by sorry
theorem summable_Lp_add_of_nonneg (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    Summable fun i => (f i + g i) ^ p :=
  (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).1

theorem Lp_add_le_tsum_of_nonneg' (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).2

/-- **Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `ℝ`-valued functions. For an alternative version, convenient if the infinite
sums are not already expressed as `p`-th powers, see `Lp_add_le_tsum_of_nonneg`. -/
theorem Lp_add_le_hasSum_of_nonneg (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hfA : HasSum (fun i => f i ^ p) (A ^ p))
    (hgB : HasSum (fun i => g i ^ p) (B ^ p)) :
    ∃ C, 0 ≤ C ∧ C ≤ A + B ∧ HasSum (fun i => (f i + g i) ^ p) (C ^ p) := by sorry
end Real

namespace ENNReal

variable (f g : ι → ℝ≥0∞) {p q : ℝ}

-- TODO: fix the non-terminal simp on the last line
set_option linter.flexible false in
/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0∞`-valued functions. -/
theorem inner_le_Lp_mul_Lq (hpq : p.HolderConjugate q) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by sorry
lemma inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) (w f : ι → ℝ≥0∞) :
    ∑ i ∈ s, w i * f i ≤ (∑ i ∈ s, w i) ^ (1 - p⁻¹) * (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ := by sorry
theorem rpow_sum_le_const_mul_sum_rpow (hp : 1 ≤ p) :
    (∑ i ∈ s, f i) ^ p ≤ (card s : ℝ≥0∞) ^ (p - 1) * ∑ i ∈ s, f i ^ p := by sorry
theorem Lp_add_le (hp : 1 ≤ p) :
    (∑ i ∈ s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) + (∑ i ∈ s, g i ^ p) ^ (1 / p) := by sorry
end ENNReal

end HoelderMinkowski
