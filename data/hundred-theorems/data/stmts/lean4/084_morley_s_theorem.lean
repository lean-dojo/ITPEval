-- Statement-only formalization of "Morley's Theorem" from Hundred Theorems item 084.
-- The adjacent internal angle trisectors of a nondegenerate real-plane triangle meet in an
-- equilateral triangle. This file contains no proof.

import Mathlib.Geometry.Euclidean.Triangle

open Set

open scoped EuclideanGeometry

namespace Theorems100

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Morley's theorem: the intersections of adjacent internal angle trisectors form an
equilateral triangle. -/
theorem morley (a b c p q r : Plane)
    (h_noncollinear : ¬Collinear ℝ ({a, b, c} : Set Plane))
    (h_interior : ({p, q, r} : Set Plane) ⊆ convexHull ℝ ({a, b, c} : Set Plane))
    (h_abr : ∠ a b r = ∠ a b c / 3)
    (h_bar : ∠ b a r = ∠ b a c / 3)
    (h_bcp : ∠ b c p = ∠ b c a / 3)
    (h_cbp : ∠ c b p = ∠ c b a / 3)
    (h_caq : ∠ c a q = ∠ c a b / 3)
    (h_acq : ∠ a c q = ∠ a c b / 3) :
    dist r p = dist p q ∧ dist q r = dist p q := sorry

end Theorems100
