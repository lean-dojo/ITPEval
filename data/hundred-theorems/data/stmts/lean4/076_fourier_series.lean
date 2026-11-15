/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!

# Fourier analysis on the additive circle

This file contains basic results on Fourier series for functions on the additive circle
`AddCircle T = ℝ / ℤ • T`.

## Main definitions

* `haarAddCircle`, Haar measure on `AddCircle T`, normalized to have total measure `1`.
  Note that this is not the same normalisation
  as the standard measure defined in `IntervalIntegral.Periodic`,
  so we do not declare it as a `MeasureSpace` instance, to avoid confusion.
* for `n : ℤ`, `fourier n` is the monomial `fun x => exp (2 π i n x / T)`,
  bundled as a continuous map from `AddCircle T` to `ℂ`.
* `fourierBasis` is the Hilbert basis of `Lp ℂ 2 haarAddCircle` given by the images of the
  monomials `fourier n`.
* `fourierCoeff f n`, for `f : AddCircle T → E` (with `E` a complete normed `ℂ`-vector space), is
  the `n`-th Fourier coefficient of `f`, defined as an integral over `AddCircle T`. The lemma
  `fourierCoeff_eq_intervalIntegral` expresses this as an integral over `[a, a + T]` for any real
  `a`.
* `fourierCoeffOn`, for `f : ℝ → E` and `a < b` reals, is the `n`-th Fourier
  coefficient of the unique periodic function of period `b - a` which agrees with `f` on `(a, b]`.
  The lemma `fourierCoeffOn_eq_integral` expresses this as an integral over `[a, b]`.

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(AddCircle T, ℂ)`, i.e. that its `Submodule.topologicalClosure` is `⊤`.  This follows
from the Stone-Weierstrass theorem after checking that the span is a subalgebra, is closed under
conjugation, and separates points.

Using this and general theory on approximation of Lᵖ functions by continuous functions, we deduce
(`span_fourierLp_closure_eq_top`) that for any `1 ≤ p < ∞`, the span of the Fourier monomials is
dense in the Lᵖ space of `AddCircle T`. For `p = 2` we show (`orthonormal_fourier`) that the
monomials are also orthonormal, so they form a Hilbert basis for L², which is named as
`fourierBasis`; in particular, for `L²` functions `f`, the Fourier series of `f` converges to `f`
in the `L²` topology (`hasSum_fourier_series_L2`). Parseval's identity, `hasSum_sq_fourierCoeff`, is
a direct consequence.

For continuous maps `f : AddCircle T → ℂ`, the theorem
`hasSum_fourier_series_of_summable` states that if the sequence of Fourier
coefficients of `f` is summable, then the Fourier series `∑ (i : ℤ), fourierCoeff f i * fourier i`
converges to `f` in the uniform-convergence topology of `C(AddCircle T, ℂ)`.
-/

@[expose] public section


noncomputable section

open scoped ENNReal ComplexConjugate Real

open TopologicalSpace ContinuousMap MeasureTheory MeasureTheory.Measure Algebra Submodule Set

variable {T : ℝ}

namespace AddCircle

/-! ### Measure on `AddCircle T`

In this file we use the Haar measure on `AddCircle T` normalised to have total measure 1 (which is
**not** the same as the standard measure defined in `Topology.Instances.AddCircle`). -/

variable [hT : Fact (0 < T)]

/-- Haar measure on the additive circle, normalised to have total measure 1. -/
def haarAddCircle : Measure (AddCircle T) :=
  addHaarMeasure ⊤
deriving IsAddHaarMeasure

instance : IsProbabilityMeasure (@haarAddCircle T _) :=
  IsProbabilityMeasure.mk addHaarMeasure_self

theorem volume_eq_smul_haarAddCircle :
    (volume : Measure (AddCircle T)) = ENNReal.ofReal T • (@haarAddCircle T _) :=
  rfl

lemma integral_haarAddCircle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : AddCircle T → E} : ∫ t, f t ∂haarAddCircle = T⁻¹ • ∫ t, f t := by sorry
end AddCircle

namespace MeasureTheory

lemma memLp_haarAddCircle_iff [hT : Fact (0 < T)] {f : AddCircle T → ℂ} {p : ℝ≥0∞} :
    MemLp f p AddCircle.haarAddCircle ↔ MemLp f p := by sorry
end MeasureTheory

open AddCircle

section Monomials

/-- The family of exponential monomials `fun x => exp (2 π i n x / T)`, parametrized by `n : ℤ` and
considered as bundled continuous maps from `ℝ / ℤ • T` to `ℂ`. -/
def fourier (n : ℤ) : C(AddCircle T, ℂ) where
  toFun x := toCircle (n • x :)
  continuous_toFun := continuous_induced_dom.comp <| continuous_toCircle.comp <| continuous_zsmul _

@[simp]
theorem fourier_apply {n : ℤ} {x : AddCircle T} : fourier n x = toCircle (n • x :) :=
  rfl

-- simp normal form is `fourier_coe_apply'`
theorem fourier_coe_apply {n : ℤ} {x : ℝ} :
    fourier n (x : AddCircle T) = Complex.exp (2 * π * Complex.I * n * x / T) := by sorry
theorem fourier_coe_apply' {n : ℤ} {x : ℝ} :
    toCircle (n • (x : AddCircle T) :) = Complex.exp (2 * π * Complex.I * n * x / T) := by sorry
theorem fourier_zero {x : AddCircle T} : fourier 0 x = 1 := by sorry
theorem fourier_zero' : @toCircle T 0 = (1 : ℂ) := by sorry
theorem fourier_eval_zero (n : ℤ) : fourier n (0 : AddCircle T) = 1 := by sorry
theorem fourier_one {x : AddCircle T} : fourier 1 x = toCircle x := by rw [fourier_apply, one_zsmul]

-- simp normal form is `fourier_neg'`
theorem fourier_neg {n : ℤ} {x : AddCircle T} : fourier (-n) x = conj (fourier n x) := by sorry
theorem fourier_neg' {n : ℤ} {x : AddCircle T} : @toCircle T (-(n • x)) = conj (fourier n x) := by sorry
theorem fourier_add {m n : ℤ} {x : AddCircle T} :
    fourier (m + n) x = fourier m x * fourier n x := by sorry
theorem fourier_add' {m n : ℤ} {x : AddCircle T} :
    toCircle ((m + n) • x :) = fourier m x * fourier n x := by sorry
theorem fourier_norm [Fact (0 < T)] (n : ℤ) : ‖@fourier T n‖ = 1 := by sorry
theorem fourier_add_half_inv_index {n : ℤ} (hn : n ≠ 0) (hT : 0 < T) (x : AddCircle T) :
    @fourier T n (x + ↑(T / 2 / n)) = -fourier n x := by sorry
def fourierSubalgebra : StarSubalgebra ℂ C(AddCircle T, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range fourier)
  star_mem' := by sorry
theorem fourierSubalgebra_coe :
    Subalgebra.toSubmodule (@fourierSubalgebra T).toSubalgebra = span ℂ (range (@fourier T)) := by sorry
variable [hT : Fact (0 < T)]

/-- The subalgebra of `C(AddCircle T, ℂ)` generated by `fourier n` for `n ∈ ℤ`
separates points. -/
theorem fourierSubalgebra_separatesPoints : (@fourierSubalgebra T).SeparatesPoints := by sorry
theorem fourierSubalgebra_closure_eq_top : (@fourierSubalgebra T).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints fourierSubalgebra
    fourierSubalgebra_separatesPoints

/-- The linear span of the monomials `fourier n` is dense in `C(AddCircle T, ℂ)`. -/
theorem span_fourier_closure_eq_top : (span ℂ (range <| @fourier T)).topologicalClosure = ⊤ := by sorry
abbrev fourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) : Lp ℂ p (@haarAddCircle T hT) :=
  toLp (E := ℂ) p haarAddCircle ℂ (fourier n)

theorem coeFn_fourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :
    @fourierLp T hT p _ n =ᵐ[haarAddCircle] fourier n :=
  coeFn_toLp haarAddCircle (fourier n)

/-- For each `1 ≤ p < ∞`, the linear span of the monomials `fourier n` is dense in
`Lp ℂ p haarAddCircle`. -/
theorem span_fourierLp_closure_eq_top {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (span ℂ (range (@fourierLp T _ p _))).topologicalClosure = ⊤ := by sorry
theorem orthonormal_fourier : Orthonormal ℂ (@fourierLp T _ 2 _) := by sorry
end Monomials

section ScopeHT

-- everything from here on needs `0 < T`
variable [hT : Fact (0 < T)]

section fourierCoeff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The `n`-th Fourier coefficient of a function `AddCircle T → E`, for `E` a complete normed
`ℂ`-vector space, defined as the integral over `AddCircle T` of `fourier (-n) t • f t`. -/
def fourierCoeff (f : AddCircle T → E) (n : ℤ) : E :=
  ∫ t : AddCircle T, fourier (-n) t • f t ∂haarAddCircle

/-- The Fourier coefficients of a function on `AddCircle T` can be computed as an integral
over `[a, a + T]`, for any real `a`. -/
theorem fourierCoeff_eq_intervalIntegral (f : AddCircle T → E) (n : ℤ) (a : ℝ) :
    fourierCoeff f n = (1 / T) • ∫ x in a..a + T, @fourier T (-n) x • f x := by sorry
theorem MeasureTheory.Integrable.fourier_smul {f : AddCircle T → E}
    (hf : Integrable f haarAddCircle) (n : ℤ) :
    Integrable (fun t ↦ fourier n t • f t) haarAddCircle := by sorry
theorem fourierCoeff.add {f g : AddCircle T → E} (hf : Integrable f haarAddCircle)
    (hg : Integrable g haarAddCircle) :
    fourierCoeff (f + g) = fourierCoeff f + fourierCoeff g := by sorry
theorem fourierCoeff.sum {ι : Type*} (s : Finset ι) (f : ι → AddCircle T → E)
    (hf : ∀ i ∈ s, Integrable (f i) haarAddCircle) :
    fourierCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, fourierCoeff (f i) := by sorry
theorem fourierCoeff.const_smul (f : AddCircle T → E) (c : ℂ) (n : ℤ) :
    fourierCoeff (c • f :) n = c • fourierCoeff f n := by sorry
theorem fourierCoeff.const_mul (f : AddCircle T → ℂ) (c : ℂ) (n : ℤ) :
    fourierCoeff (fun x => c * f x) n = c * fourierCoeff f n :=
  fourierCoeff.const_smul f c n

lemma fourierCoeff_congr_ae {f g : AddCircle T → E}
    (h : f =ᵐ[haarAddCircle] g) : fourierCoeff f = fourierCoeff g :=
  funext fun _ ↦ integral_congr_ae <| .smul (.refl _ _) h

/-- For a function on `ℝ`, the Fourier coefficients of `f` on `[a, b]` are defined as the
Fourier coefficients of the unique periodic function agreeing with `f` on `Ioc a b`. -/
def fourierCoeffOn {a b : ℝ} (hab : a < b) (f : ℝ → E) (n : ℤ) : E :=
  haveI := Fact.mk (by linarith : 0 < b - a)
  fourierCoeff (AddCircle.liftIoc (b - a) a f) n

theorem fourierCoeffOn_eq_integral {a b : ℝ} (f : ℝ → E) (n : ℤ) (hab : a < b) :
    fourierCoeffOn hab f n =
      (1 / (b - a)) • ∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • f x := by sorry
theorem fourierCoeffOn.const_smul {a b : ℝ} (f : ℝ → E) (c : ℂ) (n : ℤ) (hab : a < b) :
    fourierCoeffOn hab (c • f) n = c • fourierCoeffOn hab f n := by sorry
theorem fourierCoeffOn.const_mul {a b : ℝ} (f : ℝ → ℂ) (c : ℂ) (n : ℤ) (hab : a < b) :
    fourierCoeffOn hab (fun x => c * f x) n = c * fourierCoeffOn hab f n :=
  fourierCoeffOn.const_smul _ _ _ _

lemma fourierCoeffOn_congr_ae {a b : ℝ} (hab : a < b) {f g : ℝ → E}
    (h : f =ᵐ[volume.restrict (Ioc a b)] g) :
    fourierCoeffOn hab f = fourierCoeffOn hab g := by sorry
theorem fourierCoeff_liftIoc_eq {a : ℝ} (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (AddCircle.liftIoc T a f) n =
    fourierCoeffOn (lt_add_of_pos_right a hT.out) f n := by sorry
theorem fourierCoeff_liftIco_eq {a : ℝ} (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (AddCircle.liftIco T a f) n =
    fourierCoeffOn (lt_add_of_pos_right a hT.out) f n := by sorry
end fourierCoeff

section FourierL2

/-- We define `fourierBasis` to be a `ℤ`-indexed Hilbert basis for `Lp ℂ 2 haarAddCircle`,
which by definition is an isometric isomorphism from `Lp ℂ 2 haarAddCircle` to `ℓ²(ℤ, ℂ)`. -/
def fourierBasis : HilbertBasis ℤ ℂ (Lp ℂ 2 <| @haarAddCircle T hT) :=
  HilbertBasis.mk orthonormal_fourier (span_fourierLp_closure_eq_top (by simp)).ge

/-- The elements of the Hilbert basis `fourierBasis` are the functions `fourierLp 2`, i.e. the
monomials `fourier n` on the circle considered as elements of `L²`. -/
@[simp]
theorem coe_fourierBasis : ⇑(@fourierBasis T hT) = @fourierLp T hT 2 _ :=
  HilbertBasis.coe_mk _ _

set_option backward.isDefEq.respectTransparency false in
/-- Under the isometric isomorphism `fourierBasis` from `Lp ℂ 2 haarAddCircle` to `ℓ²(ℤ, ℂ)`, the
`i`-th coefficient is `fourierCoeff f i`, i.e., the integral over `AddCircle T` of
`fun t => fourier (-i) t * f t` with respect to the Haar measure of total mass 1. -/
theorem fourierBasis_repr (f : Lp ℂ 2 <| @haarAddCircle T hT) (i : ℤ) :
    fourierBasis.repr f i = fourierCoeff f i := by sorry
theorem hasSum_fourier_series_L2 (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    HasSum (fun i => fourierCoeff f i • fourierLp 2 i) f := by sorry
theorem hasSum_sq_fourierCoeff (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    HasSum (fun i => ‖fourierCoeff f i‖ ^ 2) (∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle) := by sorry
theorem tsum_sq_fourierCoeff (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ∑' i : ℤ, ‖fourierCoeff f i‖ ^ 2 = ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle :=
  (hasSum_sq_fourierCoeff _).tsum_eq

/-- **Parseval's identity**: for a function `f` which is square integrable on `(a,b]`,
the sum of the squared norms of the Fourier coefficients equals the `L²` norm of `f`. -/
theorem hasSum_sq_fourierCoeffOn
    {a b : ℝ} {f : ℝ → ℂ} (hab : a < b) (hL2 : MemLp f 2 (volume.restrict (Ioc a b))) :
    HasSum (fun i => ‖fourierCoeffOn hab f i‖ ^ 2) ((b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2) := by sorry
theorem tsum_sq_fourierCoeffOn
    {a b : ℝ} {f : ℝ → ℂ} (hab : a < b) (hL2 : MemLp f 2 (volume.restrict (Ioc a b))) :
    ∑' (i : ℤ), ‖fourierCoeffOn hab f i‖ ^ 2 = (b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2 :=
  (hasSum_sq_fourierCoeffOn _ hL2).tsum_eq

end FourierL2

section Convergence

variable (f : C(AddCircle T, ℂ))

theorem fourierCoeff_toLp (n : ℤ) :
    fourierCoeff (toLp (E := ℂ) 2 haarAddCircle ℂ f) n = fourierCoeff f n :=
  integral_congr_ae (Filter.EventuallyEq.mul (Filter.Eventually.of_forall (by tauto))
    (ContinuousMap.coeFn_toAEEqFun haarAddCircle f))

variable {f}

set_option backward.isDefEq.respectTransparency false in
/-- If the sequence of Fourier coefficients of `f` is summable, then the Fourier series converges
uniformly to `f`. -/
theorem hasSum_fourier_series_of_summable (h : Summable (fourierCoeff f)) :
    HasSum (fun i => fourierCoeff f i • fourier i) f := by sorry
theorem has_pointwise_sum_fourier_series_of_summable (h : Summable (fourierCoeff f))
    (x : AddCircle T) : HasSum (fun i => fourierCoeff f i • fourier i x) (f x) := by sorry
end Convergence

end ScopeHT

section computations

theorem fourierCoeff_fourier {T : ℝ} [hT : Fact (0 < T)] (n : ℤ) :
    fourierCoeff (T := T) (fourier n) = Pi.single n 1 := by sorry
end computations

section deriv

open Complex intervalIntegral

open scoped Interval

variable (T)

theorem hasDerivAt_fourier (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fourier n (y : AddCircle T))
      (2 * π * I * n / T * fourier n (x : AddCircle T)) x := by sorry
theorem hasDerivAt_fourier_neg (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fourier (-n) (y : AddCircle T))
      (-2 * π * I * n / T * fourier (-n) (x : AddCircle T)) x := by sorry
variable {T}

theorem has_antideriv_at_fourier_neg (hT : Fact (0 < T)) {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (T : ℂ) / (-2 * π * I * n) * fourier (-n) (y : AddCircle T))
      (fourier (-n) (x : AddCircle T)) x := by sorry
theorem fourierCoeffOn_of_hasDeriv_right {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    {n : ℤ} (hn : n ≠ 0)
    (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x, x ∈ Ioo (min a b) (max a b) → HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n = 1 / (-2 * π * I * n) *
      (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) - (b - a) * fourierCoeffOn hab f' n) := by sorry
theorem fourierCoeffOn_of_hasDerivAt_Ioo {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    {n : ℤ} (hn : n ≠ 0)
    (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x, x ∈ Ioo (min a b) (max a b) → HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n = 1 / (-2 * π * I * n) *
      (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) - (b - a) * fourierCoeffOn hab f' n) :=
  fourierCoeffOn_of_hasDeriv_right hab hn hf (fun x hx ↦ hff' x hx |>.hasDerivWithinAt) hf'

/-- Express Fourier coefficients of `f` on an interval in terms of those of its derivative. -/
theorem fourierCoeffOn_of_hasDerivAt {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x, x ∈ [[a, b]] → HasDerivAt f (f' x) x) (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n = 1 / (-2 * π * I * n) *
      (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) - (b - a) * fourierCoeffOn hab f' n) :=
  fourierCoeffOn_of_hasDerivAt_Ioo hab hn
    (fun x hx ↦ hf x hx |>.continuousAt.continuousWithinAt)
    (fun x hx ↦ hf x <| mem_Icc_of_Ioo hx)
    hf'

end deriv
