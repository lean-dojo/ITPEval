/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries

/-!
# Critical values of the Riemann zeta function

In this file we prove formulae for the critical values of `ζ(s)`, and more generally of Hurwitz
zeta functions, in terms of Bernoulli polynomials.

## Main results:

* `hasSum_zeta_nat`: the final formula for zeta values,
  $$\zeta(2k) = \frac{(-1)^{(k + 1)} 2 ^ {2k - 1} \pi^{2k} B_{2 k}}{(2 k)!}.$$
* `hasSum_zeta_two` and `hasSum_zeta_four`: special cases given explicitly.
* `hasSum_one_div_nat_pow_mul_cos`: a formula for the sum `∑ (n : ℕ), cos (2 π i n x) / n ^ k` as
  an explicit multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 2` even.
* `hasSum_one_div_nat_pow_mul_sin`: a formula for the sum `∑ (n : ℕ), sin (2 π i n x) / n ^ k` as
  an explicit multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 3` odd.
-/

@[expose] public section

noncomputable section

open scoped Nat Real Interval

open Complex MeasureTheory Set intervalIntegral

local notation "𝕌" => UnitAddCircle

section BernoulliFunProps

/-! Simple properties of the Bernoulli polynomial, as a function `ℝ → ℝ`. -/


/-- The function `x ↦ Bₖ(x) : ℝ → ℝ`. -/
def bernoulliFun (k : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli k)).eval x

section Evaluation

@[simp]
theorem bernoulliFun_zero (x : ℝ) : bernoulliFun 0 x = 1 := by sorry
theorem bernoulliFun_one (x : ℝ) : bernoulliFun 1 x = x - 1 / 2 := by sorry
theorem bernoulliFun_two (x : ℝ) : bernoulliFun 2 x = x ^ 2 - x + 6⁻¹ := by sorry
theorem bernoulliFun_eval_zero (k : ℕ) : bernoulliFun k 0 = bernoulli k := by sorry
theorem bernoulliFun_endpoints_eq_of_ne_one {k : ℕ} (hk : k ≠ 1) :
    bernoulliFun k 1 = bernoulliFun k 0 := by sorry
theorem bernoulliFun_eval_one (k : ℕ) : bernoulliFun k 1 = bernoulliFun k 0 + ite (k = 1) 1 0 := by sorry
end Evaluation

section Calculus

theorem hasDerivAt_bernoulliFun (k : ℕ) (x : ℝ) :
    HasDerivAt (bernoulliFun k) (k * bernoulliFun (k - 1) x) x := by sorry
variable (k : ℕ)

theorem contDiff_bernoulliFun : ContDiff ℝ ⊤ (bernoulliFun k) := by sorry
theorem continuous_bernoulliFun : Continuous (bernoulliFun k) := Polynomial.continuous_aeval _

theorem intervalIntegrable_bernoulliFun (a b : ℝ) :
    IntervalIntegrable (bernoulliFun k) volume a b :=
  (continuous_bernoulliFun k).intervalIntegrable a b

@[simp]
theorem deriv_bernoulliFun :
    deriv (bernoulliFun k) = fun x ↦ k * bernoulliFun (k - 1) x := by sorry
theorem antideriv_bernoulliFun (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x => bernoulliFun (k + 1) x / (k + 1)) (bernoulliFun k x) x := by sorry
theorem integral_bernoulliFun : ∫ x : ℝ in 0..1, bernoulliFun k x = if k = 0 then 1 else 0 := by sorry
variable {k} in
theorem integral_bernoulliFun_eq_zero (hk : k ≠ 0) :
    ∫ x : ℝ in 0..1, bernoulliFun k x = 0 := by sorry
theorem bernoulliFun_eq_integral (k : ℕ) (x y : ℝ) :
    bernoulliFun (k + 1) y =
      bernoulliFun (k + 1) x + ∫ t in x..y, (k + 1 : ℕ) * bernoulliFun k t := by sorry
end Calculus

/-- Reflection principle: `B_s(1 - x) = (-1)^s B_s(x)` -/
theorem bernoulliFun_eval_one_sub {k : ℕ} {x : ℝ} :
    bernoulliFun k (1 - x) = (-1) ^ k * bernoulliFun k x := by sorry
theorem bernoulliFun_mul (k : ℕ) {m : ℕ} (m0 : m ≠ 0) (x : ℝ) :
    bernoulliFun k (m * x) =
      m ^ k / m * ∑ i ∈ Finset.range m, bernoulliFun k (x + i / m) := by sorry
theorem bernoulliFun_eval_half_eq_zero (k : ℕ) : bernoulliFun (2 * k + 1) 2⁻¹ = 0 := by sorry
theorem bernoulliFun_eval_half (k : ℕ) : bernoulliFun k 2⁻¹ = (2 / 2 ^ k - 1) * bernoulli k := by sorry
end BernoulliFunProps

section BernoulliFourierCoeffs

/-! Compute the Fourier coefficients of the Bernoulli functions via integration by parts. -/


/-- The `n`-th Fourier coefficient of the `k`-th Bernoulli function on the interval `[0, 1]`. -/
def bernoulliFourierCoeff (k : ℕ) (n : ℤ) : ℂ :=
  fourierCoeffOn zero_lt_one (fun x => bernoulliFun k x) n

/-- Recurrence relation (in `k`) for the `n`-th Fourier coefficient of `Bₖ`. -/
theorem bernoulliFourierCoeff_recurrence (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
    bernoulliFourierCoeff k n =
      1 / (-2 * π * I * n) * (ite (k = 1) 1 0 - k * bernoulliFourierCoeff (k - 1) n) := by sorry
theorem bernoulli_zero_fourier_coeff {n : ℤ} (hn : n ≠ 0) : bernoulliFourierCoeff 0 n = 0 := by sorry
theorem bernoulliFourierCoeff_zero {k : ℕ} (hk : k ≠ 0) : bernoulliFourierCoeff k 0 = 0 := by sorry
theorem bernoulliFourierCoeff_eq {k : ℕ} (hk : k ≠ 0) (n : ℤ) :
    bernoulliFourierCoeff k n = -k ! / (2 * π * I * n) ^ k := by sorry
end BernoulliFourierCoeffs

section BernoulliPeriodized

/-! In this section we use the above evaluations of the Fourier coefficients of Bernoulli
polynomials, together with the theorem `has_pointwise_sum_fourier_series_of_summable` from Fourier
theory, to obtain an explicit formula for `∑ (n:ℤ), 1 / n ^ k * fourier n x`. -/


/-- The Bernoulli polynomial, extended from `[0, 1)` to the unit circle. -/
def periodizedBernoulli (k : ℕ) : 𝕌 → ℝ :=
  AddCircle.liftIco 1 0 (bernoulliFun k)

theorem periodizedBernoulli.continuous {k : ℕ} (hk : k ≠ 1) : Continuous (periodizedBernoulli k) :=
  AddCircle.liftIco_zero_continuous
    (mod_cast (bernoulliFun_endpoints_eq_of_ne_one hk).symm)
    (Polynomial.continuous _).continuousOn

theorem fourierCoeff_bernoulli_eq {k : ℕ} (hk : k ≠ 0) (n : ℤ) :
    fourierCoeff ((↑) ∘ periodizedBernoulli k : 𝕌 → ℂ) n = -k ! / (2 * π * I * n) ^ k := by sorry
theorem summable_bernoulli_fourier {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun n => -k ! / (2 * π * I * n) ^ k : ℤ → ℂ) := by sorry
theorem hasSum_one_div_pow_mul_fourier_mul_bernoulliFun {k : ℕ} (hk : 2 ≤ k) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℤ => 1 / (n : ℂ) ^ k * fourier n (x : 𝕌))
      (-(2 * π * I) ^ k / k ! * bernoulliFun k x) := by sorry
end BernoulliPeriodized

section Cleanup

-- This section is just reformulating the results in a nicer form.
theorem hasSum_one_div_nat_pow_mul_fourier {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum
      (fun n : ℕ =>
        (1 : ℂ) / (n : ℂ) ^ k * (fourier n (x : 𝕌) + (-1 : ℂ) ^ k * fourier (-n) (x : 𝕌)))
      (-(2 * π * I) ^ k / k ! * bernoulliFun k x) := by sorry
theorem hasSum_one_div_nat_pow_mul_cos {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * π * n * x))
      ((-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
        (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * k))).eval x) := by sorry
theorem hasSum_one_div_nat_pow_mul_sin {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k + 1) * Real.sin (2 * π * n * x))
      ((-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k + 1) / 2 / (2 * k + 1)! *
        (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * k + 1))).eval x) := by sorry
theorem hasSum_zeta_nat {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k))
      ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) *
        bernoulli (2 * k) / (2 * k)!) := by sorry
end Cleanup

section Examples

theorem hasSum_zeta_two : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6) := by sorry
theorem hasSum_zeta_four : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) (π ^ 4 / 90) := by sorry
theorem hasSum_L_function_mod_four_eval_three :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3 * Real.sin (π * n / 2)) (π ^ 3 / 32) := by sorry
end Examples
