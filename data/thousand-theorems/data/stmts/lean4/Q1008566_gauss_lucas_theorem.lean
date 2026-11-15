-- Statement-only formalization of Thousand Theorems artifact Q1008566
-- (thousand-theorems__lean4__Q1008566), "Gauss–Lucas theorem": roots of the derivative
-- of a nonconstant complex polynomial lie in the convex hull of its roots, with an explicit
-- center-of-mass formula for each derivative root. This file contains no proof.

import Mathlib.Analysis.Complex.Polynomial.Basic

open scoped Polynomial ComplexConjugate

namespace Polynomial

/-- The weight of a root in the center-of-mass formula for a root of the derivative. -/
noncomputable def derivRootWeight (P : ℂ[X]) (z w : ℂ) : ℝ :=
  if P.eval z = 0 then (Pi.single z 1 : ℂ → ℝ) w
  else P.rootMultiplicity w / ‖z - w‖ ^ 2

variable {P : ℂ[X]} {z : ℂ}

/-- A root of the derivative is the specified weighted center of mass of the roots. -/
theorem eq_centerMass_of_eval_derivative_eq_zero (hP : 0 < P.degree)
    (hz : P.derivative.eval z = 0) :
    z = P.roots.toFinset.centerMass (P.derivRootWeight z) id := sorry

/-- The Gauss–Lucas theorem for nonconstant complex polynomials. -/
theorem rootSet_derivative_subset_convexHull_rootSet (h₀ : 0 < P.degree) :
    P.derivative.rootSet ℂ ⊆ convexHull ℝ (P.rootSet ℂ) := sorry

end Polynomial
