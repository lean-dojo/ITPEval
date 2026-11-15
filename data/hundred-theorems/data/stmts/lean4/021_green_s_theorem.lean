-- Statement-only formalization of "Green's Theorem" from Hundred Theorems item 021.
-- It gives the winding-number form for closed absolutely continuous plane curves.
-- This file contains no proof.

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

noncomputable section

open Set

@[expose] public section

namespace HundredTheorems.GreenTheorem

/-- The image of the unit-interval parametrization of a complex plane curve. -/
def pathImage (g : ℝ → ℂ) : Set ℂ :=
  g '' Icc (0 : ℝ) 1

/--
The inside of a curve: the points off the curve lying in bounded connected
components of its complement.
-/
def curveInside (g : ℝ → ℂ) : Set ℂ :=
  {z | z ∉ pathImage g ∧
    Bornology.IsBounded (connectedComponentIn (pathImage g)ᶜ z)}

/-- The native interval-integral integrand for the complex line integral. -/
def pathIntegrand (g : ℝ → ℂ) (f : ℂ → ℂ) (t : ℝ) : ℂ :=
  f (g t) * deriv g t

/-- The complex line integral of `f` along `g` on `[0, 1]`. -/
def pathIntegral (g : ℝ → ℂ) (f : ℂ → ℂ) : ℂ :=
  intervalIntegral (pathIntegrand g f) 0 1 MeasureTheory.volume

/-- Native interval integrability of the line-integral integrand. -/
def PathIntegrable (g : ℝ → ℂ) (f : ℂ → ℂ) : Prop :=
  IntervalIntegrable (pathIntegrand g f) MeasureTheory.volume 0 1

/-- Native whole-plane integrability with respect to Lebesgue measure on `ℂ`. -/
def PlaneIntegrable (f : ℂ → ℂ) : Prop :=
  MeasureTheory.Integrable f MeasureTheory.volume

/-- The native whole-plane integral with respect to Lebesgue measure on `ℂ`. -/
def planeIntegral (f : ℂ → ℂ) : ℂ :=
  MeasureTheory.integral MeasureTheory.volume f

/-- The winding number normalized by Mathlib's standard real circle constant. -/
def windingNumber (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    pathIntegral g (fun w => (w - z)⁻¹)

/-- The Wirtinger derivative `∂f/∂z̄` of a real-differentiable complex map. -/
def wirtingerDbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ *
    (fderiv ℝ f z (1 : ℂ) + Complex.I * fderiv ℝ f z Complex.I)

/--
Green's theorem for an absolutely continuous closed plane curve. The winding
number records the oriented multiplicity with which the curve surrounds each
point.
-/
theorem greens_theorem
    (f : ℂ → ℂ) (g : ℝ → ℂ) (u : Set ℂ)
    (hg_ac : AbsolutelyContinuousOnInterval g 0 1)
    (hg_closed : g 1 = g 0)
    (hu_open : IsOpen u)
    (hu_contains : curveInside g ∪ pathImage g ⊆ u)
    (hf_diff : DifferentiableOn ℝ f u)
    (hf_fderiv_cont :
      ∀ h : ℂ, ContinuousOn (fun z => fderiv ℝ f z h) u) :
    PlaneIntegrable
        (fun z => windingNumber g z * wirtingerDbar f z) ∧
      PathIntegrable g f ∧
      pathIntegral g f =
        (2 : ℂ) * Complex.I *
          planeIntegral (fun z => windingNumber g z * wirtingerDbar f z) :=
  sorry

end HundredTheorems.GreenTheorem
