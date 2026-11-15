/-
Copyright (c) 2021 James Arthur, Benjamin Davidson, Andrew Souther. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Benjamin Davidson, Andrew Souther
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Freek № 9: The Area of a Circle

In this file we show that the area of a disc with nonnegative radius `r` is `π * r^2`. The main
tools our proof uses are `volume_regionBetween_eq_integral`, which allows us to represent the area
of the disc as an integral, and `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, the
second fundamental theorem of calculus.

We begin by defining `disc` in `ℝ × ℝ`, then show that `disc` can be represented as the
`regionBetween` two functions.

Though not necessary for the main proof, we nonetheless choose to include a proof of the
measurability of the disc in order to convince the reader that the set whose volume we will be
calculating is indeed measurable and our result is therefore meaningful.

In the main proof, `area_disc`, we use `volume_regionBetween_eq_integral` followed by
`intervalIntegral.integral_of_le` to reduce our goal to a single `intervalIntegral`:
  `∫ (x : ℝ) in -r..r, 2 * sqrt (r ^ 2 - x ^ 2) = π * r ^ 2`.
After disposing of the trivial case `r = 0`, we show that `fun x => 2 * sqrt (r ^ 2 - x ^ 2)` is
equal to the derivative of `fun x => r ^ 2 * arcsin (x / r) + x * sqrt (r ^ 2 - x ^ 2)` everywhere
on `Ioo (-r) r` and that those two functions are continuous, then apply the second fundamental
theorem of calculus with those facts. Some simple algebra then completes the proof.

Note that we choose to define `disc` as a set of points in `ℝ × ℝ`. This is admittedly not ideal; it
would be more natural to define `disc` as a `Metric.ball` in `EuclideanSpace ℝ (Fin 2)` (as well as
to provide a more general proof in higher dimensions). However, our proof indirectly relies on a
number of theorems (particularly `MeasureTheory.Measure.prod_apply`) which do not yet exist for
Euclidean space, thus forcing us to use this less-preferable definition. As `MeasureTheory.pi`
continues to develop, it should eventually become possible to redefine `disc` and extend our proof
to the n-ball.
-/


open Set Real MeasureTheory intervalIntegral

open scoped Real NNReal

namespace Theorems100

/-- A disc of radius `r` is defined as the collection of points `(p.1, p.2)` in `ℝ × ℝ` such that
  `p.1 ^ 2 + p.2 ^ 2 < r ^ 2`.
  Note that this definition is not equivalent to `Metric.ball (0 : ℝ × ℝ) r`. This was done
  intentionally because `dist` in `ℝ × ℝ` is defined as the uniform norm, making the `Metric.ball`
  in `ℝ × ℝ` a square, not a disc.
  See the module docstring for an explanation of why we don't define the disc in Euclidean space. -/
def disc (r : ℝ) :=
  {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}

variable (r : ℝ≥0)

/-- A disc of radius `r` can be represented as the region between the two curves
  `fun x => - sqrt (r ^ 2 - x ^ 2)` and `fun x => sqrt (r ^ 2 - x ^ 2)`. -/
theorem disc_eq_regionBetween :
    disc r =
      regionBetween
        (fun x => -sqrt (r ^ 2 - x ^ 2)) (fun x => sqrt (r ^ 2 - x ^ 2)) (Ioc (-r) r) := by sorry
theorem measurableSet_disc : MeasurableSet (disc r) := by sorry
theorem area_disc : volume (disc r) = NNReal.pi * r ^ 2 := by sorry
end Theorems100
