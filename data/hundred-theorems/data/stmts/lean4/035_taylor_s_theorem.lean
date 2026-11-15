/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Taylor's theorem

This file defines the Taylor polynomial of a real function `f : ℝ → E`,
where `E` is a normed vector space over `ℝ` and proves Taylor's theorem,
which states that if `f` is sufficiently smooth, then
`f` can be approximated by the Taylor polynomial up to an explicit error term.

## Main definitions

* `taylorCoeffWithin`: the Taylor coefficient using `iteratedDerivWithin`
* `taylorWithin`: the Taylor polynomial using `iteratedDerivWithin`

## Main statements

* `taylor_tendsto`: Taylor's theorem as a limit
* `taylor_isLittleO`: Taylor's theorem using little-o notation
* `taylor_mean_remainder`: Taylor's theorem with the general form of the remainder term
* `taylor_mean_remainder_lagrange`: Taylor's theorem with the Lagrange remainder
* `taylor_mean_remainder_cauchy`: Taylor's theorem with the Cauchy remainder
* `exists_taylor_mean_remainder_bound`: Taylor's theorem for vector-valued functions with a
  polynomial bound on the remainder
* `taylor_integral_remainder_of_absolutelyContinuous`,
  `taylor_integral_remainder`: Taylor's theorem with the integral form of the
  remainder

## TODO

* Generalization to higher dimensions

## Tags

Taylor polynomial, Taylor's theorem
-/

@[expose] public section


open scoped Interval Topology Nat

open Set

variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `k`th coefficient of the Taylor polynomial. -/
noncomputable def taylorCoeffWithin (f : ℝ → E) (k : ℕ) (s : Set ℝ) (x₀ : ℝ) : E :=
  (k ! : ℝ)⁻¹ • iteratedDerivWithin k f s x₀

/-- The Taylor polynomial with derivatives inside of a set `s`.

The Taylor polynomial is given by
$$∑_{k=0}^n \frac{(x - x₀)^k}{k!} f^{(k)}(x₀),$$
where $f^{(k)}(x₀)$ denotes the iterated derivative in the set `s`. -/
noncomputable def taylorWithin (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) : PolynomialModule ℝ E :=
  (Finset.range (n + 1)).sum fun k =>
    PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single ℝ k (taylorCoeffWithin f k s x₀))

/-- The Taylor polynomial with derivatives inside of a set `s` considered as a function `ℝ → E` -/
noncomputable def taylorWithinEval (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) : E :=
  PolynomialModule.eval x (taylorWithin f n s x₀)

theorem taylorWithin_succ (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) :
    taylorWithin f (n + 1) s x₀ = taylorWithin f n s x₀ +
      PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single ℝ (n + 1) (taylorCoeffWithin f (n + 1) s x₀)) := by sorry
theorem taylorWithinEval_succ (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f (n + 1) s x₀ x = taylorWithinEval f n s x₀ x +
      (((n + 1 : ℝ) * n !)⁻¹ * (x - x₀) ^ (n + 1)) • iteratedDerivWithin (n + 1) f s x₀ := by sorry
theorem taylor_within_zero_eval (f : ℝ → E) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f 0 s x₀ x = f x₀ := by sorry
theorem taylorWithinEval_self (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) :
    taylorWithinEval f n s x₀ x₀ = f x₀ := by sorry
theorem taylor_within_apply (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f n s x₀ x =
      ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * (x - x₀) ^ k) • iteratedDerivWithin k f s x₀ := by sorry
theorem continuousOn_taylorWithinEval {f : ℝ → E} {x : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hf : ContDiffOn ℝ n f s) :
    ContinuousOn (fun t => taylorWithinEval f n s t x) s := by sorry
theorem monomial_has_deriv_aux (t x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => (x - y) ^ (n + 1)) (-(n + 1) * (x - t) ^ n) t := by sorry
theorem hasDerivWithinAt_taylor_coeff_within {f : ℝ → E} {x y : ℝ} {k : ℕ} {s t : Set ℝ}
    (ht : UniqueDiffWithinAt ℝ t y) (hs : s ∈ 𝓝[t] y)
    (hf : DifferentiableWithinAt ℝ (iteratedDerivWithin (k + 1) f s) s y) :
    HasDerivWithinAt
      (fun z => (((k + 1 : ℝ) * k !)⁻¹ * (x - z) ^ (k + 1)) • iteratedDerivWithin (k + 1) f s z)
      ((((k + 1 : ℝ) * k !)⁻¹ * (x - y) ^ (k + 1)) • iteratedDerivWithin (k + 2) f s y -
        ((k ! : ℝ)⁻¹ * (x - y) ^ k) • iteratedDerivWithin (k + 1) f s y) t y := by sorry
theorem hasDerivWithinAt_taylorWithinEval {f : ℝ → E} {x y : ℝ} {n : ℕ} {s s' : Set ℝ}
    (hs_unique : UniqueDiffOn ℝ s) (hs' : s' ∈ 𝓝[s] y)
    (hy : y ∈ s') (h : s' ⊆ s) (hf : ContDiffOn ℝ n f s)
    (hf' : DifferentiableWithinAt ℝ (iteratedDerivWithin n f s) s y) :
    HasDerivWithinAt (fun t => taylorWithinEval f n s t x)
      (((n ! : ℝ)⁻¹ * (x - y) ^ n) • iteratedDerivWithin (n + 1) f s y) s' y := by sorry
theorem taylorWithinEval_hasDerivAt_Ioo {f : ℝ → E} {a b t : ℝ} (x : ℝ) {n : ℕ} (hx : a < b)
    (ht : t ∈ Ioo a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Ioo a b)) :
    HasDerivAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) t :=
  have h_nhds : Ioo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  have h_nhds' : Ioo a b ∈ 𝓝[Icc a b] t := nhdsWithin_le_nhds h_nhds
  (hasDerivWithinAt_taylorWithinEval (uniqueDiffOn_Icc hx) h_nhds' ht
    Ioo_subset_Icc_self hf <| (hf' t ht).mono_of_mem_nhdsWithin h_nhds').hasDerivAt h_nhds

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for closed intervals -/
theorem hasDerivWithinAt_taylorWithinEval_at_Icc {f : ℝ → E} {a b t : ℝ} (x : ℝ) {n : ℕ}
    (hx : a < b) (ht : t ∈ Icc a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Icc a b)) :
    HasDerivWithinAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) (Icc a b) t :=
  hasDerivWithinAt_taylorWithinEval (uniqueDiffOn_Icc hx)
    self_mem_nhdsWithin ht rfl.subset hf (hf' t ht)

/-- Calculate the derivative of the Taylor polynomial with respect to `x`. -/
theorem hasDerivAt_taylorWithinEval_succ {x₀ x : ℝ} {s : Set ℝ} (f : ℝ → E) (n : ℕ) :
    HasDerivAt (taylorWithinEval f (n + 1) s x₀)
      (taylorWithinEval (derivWithin f s) n s x₀ x) x := by sorry
theorem taylor_isLittleO {f : ℝ → E} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : Convex ℝ s) (hx₀s : x₀ ∈ s) (hf : ContDiffOn ℝ n f s) :
    (fun x ↦ f x - taylorWithinEval f n s x₀ x) =o[𝓝[s] x₀] fun x ↦ (x - x₀) ^ n := by sorry
theorem taylor_isLittleO_univ {f : ℝ → E} {x₀ : ℝ} {n : ℕ} (hf : ContDiff ℝ n f) :
    (fun x ↦ f x - taylorWithinEval f n univ x₀ x) =o[𝓝 x₀] fun x ↦ (x - x₀) ^ n := by sorry
theorem taylor_tendsto {f : ℝ → E} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : Convex ℝ s) (hx₀s : x₀ ∈ s) (hf : ContDiffOn ℝ n f s) :
    Filter.Tendsto (fun x ↦ ((x - x₀) ^ n)⁻¹ • (f x - taylorWithinEval f n s x₀ x))
      (𝓝[s] x₀) (𝓝 0) := by sorry
theorem Real.taylor_tendsto {f : ℝ → ℝ} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : Convex ℝ s) (hx₀s : x₀ ∈ s) (hf : ContDiffOn ℝ n f s) :
    Filter.Tendsto (fun x ↦ (f x - taylorWithinEval f n s x₀ x) / (x - x₀) ^ n)
      (𝓝[s] x₀) (𝓝 0) := by sorry
theorem taylor_mean_remainder {f : ℝ → ℝ} {g g' : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x))
    (gcont : ContinuousOn g (uIcc x₀ x))
    (gdiff : ∀ x_1 : ℝ, x_1 ∈ uIoo x₀ x → HasDerivAt g (g' x_1) x_1)
    (g'_ne : ∀ x_1 : ℝ, x_1 ∈ uIoo x₀ x → g' x_1 ≠ 0) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x = ((x - x') ^ n / n ! *
      (g x - g x₀) / g' x') • iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' := by sorry
theorem taylor_mean_remainder_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)! := by sorry
lemma taylor_mean_remainder_lagrange_iteratedDeriv {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ (n + 1) f (uIcc x₀ x)) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / (n + 1)! := by sorry
theorem taylor_mean_remainder_cauchy {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' * (x - x') ^ n / n ! * (x - x₀) := by sorry
theorem taylor_mean_remainder_bound {f : ℝ → E} {a b C x : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) (hx : x ∈ Icc a b)
    (hC : ∀ y ∈ Icc a b, ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤ C) :
    ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) / n ! := by sorry
theorem exists_taylor_mean_remainder_bound {f : ℝ → E} {a b : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) :
    ∃ C, ∀ x ∈ Icc a b, ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) := by sorry
theorem taylor_integral_remainder_aux [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {x x₀ : ℝ} {n : ℕ}
    (hf : ∀ k ≤ n, let u := fun t ↦ (x - t) ^ k / k !;
      let v := fun t ↦ iteratedDerivWithin k f [[x₀, x]] t;
      ∫ (t : ℝ) in x₀..x, u t • deriv v t = u x • v x - u x₀ • v x₀ -
      ∫ (t : ℝ) in x₀..x, deriv u t • v t) :
    f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / n !) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t  := by sorry
theorem taylor_integral_remainder_of_absolutelyContinuous {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
    (hf₁ : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf₂ : AbsolutelyContinuousOnInterval (iteratedDerivWithin n f (uIcc x₀ x)) x₀ x) :
    f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / n !) * iteratedDerivWithin (n + 1) f (uIcc x₀ x) t := by sorry
theorem taylor_integral_remainder [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : ℝ → F} {x x₀ : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1 : ℕ) f (uIcc x₀ x)) :
    f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / n !) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t := by sorry
