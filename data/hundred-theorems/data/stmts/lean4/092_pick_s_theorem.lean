-- Statement-only formalization of "Pick's Theorem" from Hundred Theorems item 092.
-- For a simple lattice polygon in the real plane, its area equals the number of interior
-- lattice points plus half the number of boundary lattice points minus one.
-- This file contains no proof.

import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Connected.Basic

noncomputable section

open Set

namespace Theorems100.Pick

abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A point in the real plane whose two coordinates are integers. -/
def IsLatticePoint (x : Point) : Prop :=
  ∀ coordinate, ∃ z : ℤ, x coordinate = z

/-- The next vertex in a cyclic indexing of a polygon. -/
def cyclicNext {n : ℕ} (i : Fin (n + 3)) : Fin (n + 3) :=
  i + 1

/-- The union of the closed edges of a cyclically indexed polygon. -/
def polygonBoundary {n : ℕ} (vertices : Fin (n + 3) → Point) : Set Point :=
  {x | ∃ i, x ∈ segment ℝ (vertices i) (vertices (cyclicNext i))}

/--
A polygon is simple when its vertices are distinct and two distinct closed edges meet
exactly at their shared endpoint when adjacent, and are disjoint otherwise.
-/
def IsSimplePolygon {n : ℕ} (vertices : Fin (n + 3) → Point) : Prop :=
  Function.Injective vertices ∧
    ∀ i j, i ≠ j →
      segment ℝ (vertices i) (vertices (cyclicNext i)) ∩
          segment ℝ (vertices j) (vertices (cyclicNext j)) =
        if cyclicNext i = j then
          {vertices j}
        else if cyclicNext j = i then
          {vertices i}
        else
          ∅

/-- The points off the polygon boundary lying in bounded connected components of its complement. -/
def polygonInside {n : ℕ} (vertices : Fin (n + 3) → Point) : Set Point :=
  {x |
    x ∉ polygonBoundary vertices ∧
      Bornology.IsBounded (connectedComponentIn (polygonBoundary vertices)ᶜ x)}

/-- The lattice points strictly inside a polygon. -/
def interiorLatticePoints {n : ℕ} (vertices : Fin (n + 3) → Point) : Set Point :=
  {x | x ∈ polygonInside vertices ∧ IsLatticePoint x}

/-- The lattice points on the boundary of a polygon. -/
def boundaryLatticePoints {n : ℕ} (vertices : Fin (n + 3) → Point) : Set Point :=
  {x | x ∈ polygonBoundary vertices ∧ IsLatticePoint x}

/-- Pick's theorem for arbitrary simple polygons with integral vertices. -/
theorem pick {n : ℕ} (vertices : Fin (n + 3) → Point)
    (hintegral : ∀ i, IsLatticePoint (vertices i))
    (hsimple : IsSimplePolygon vertices) :
    (MeasureTheory.volume (polygonInside vertices)).toReal =
      (interiorLatticePoints vertices).ncard +
        (boundaryLatticePoints vertices).ncard / 2 - 1 := sorry

end Theorems100.Pick
