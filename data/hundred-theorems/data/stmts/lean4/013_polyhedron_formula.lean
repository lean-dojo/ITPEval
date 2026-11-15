-- Statement-only formalization of "Polyhedron Formula" from Hundred Theorems item 013. This
-- file contains no proof.

module

public import Mathlib.Data.Real.Sqrt
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Polyhedron Formula

Euler's relation for a full-dimensional polytope in real three-space.
-/

open scoped BigOperators

namespace Theorems100.PolyhedronFormula

noncomputable section

abbrev Point := Fin 3 → ℝ

/-- The affine combination of a finite family of points with the given coefficients. -/
def weightedPoint {n : ℕ} (coefficients : Fin n → ℝ) (points : Fin n → Point) : Point :=
  fun coordinate => ∑ i, coefficients i * points i coordinate

/-- The convex hull of a finite indexed family of points. -/
def finiteConvexHull {n : ℕ} (vertices : Fin n → Point) : Set Point :=
  {x |
    ∃ coefficients : Fin n → ℝ,
      (∀ i, 0 ≤ coefficients i) ∧
        (∑ i, coefficients i) = 1 ∧
          x = weightedPoint coefficients vertices}

/-- A polytope is the convex hull of finitely many points. -/
def IsPolytope (p : Set Point) : Prop :=
  ∃ n : ℕ, ∃ vertices : Fin n → Point, p = finiteConvexHull vertices

/-- The point at parameter `t` on the segment from `x` to `y`. -/
def segmentPoint (t : ℝ) (x y : Point) : Point :=
  fun coordinate => (1 - t) * x coordinate + t * y coordinate

/-- Convexity stated directly using line segments. -/
def IsConvexSet (s : Set Point) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ∀ t : ℝ,
    0 ≤ t → t ≤ 1 → segmentPoint t x y ∈ s

/--
`f` is a face of `p` when it is a convex subset of `p` and any relative-interior
point of a segment in `p` lying in `f` forces both endpoints to lie in `f`.
-/
def IsFace (f p : Set Point) : Prop :=
  f ⊆ p ∧
    IsConvexSet f ∧
      ∀ x ∈ p, ∀ y ∈ p, ∀ t : ℝ,
        0 < t → t < 1 → segmentPoint t x y ∈ f → x ∈ f ∧ y ∈ f

/-- Affine independence via the only affine linear relation being the trivial one. -/
def AffineIndependent {n : ℕ} (points : Fin n → Point) : Prop :=
  ∀ coefficients : Fin n → ℝ,
    (∑ i, coefficients i) = 0 →
      (∀ coordinate : Fin 3, (∑ i, coefficients i * points i coordinate) = 0) →
        ∀ i, coefficients i = 0

/-- The set has affine dimension exactly `d`. -/
def AffineDimensionEq (s : Set Point) (d : ℕ) : Prop :=
  (∃ points : Fin (d + 1) → Point,
      (∀ i, points i ∈ s) ∧ AffineIndependent points) ∧
    ¬∃ points : Fin (d + 2) → Point,
      (∀ i, points i ∈ s) ∧ AffineIndependent points

/-- The set of `d`-dimensional faces of `p`. -/
def facesOfDimension (p : Set Point) (d : ℕ) : Set (Set Point) :=
  {f | IsFace f p ∧ AffineDimensionEq f d}

/--
Euler's polyhedron formula: for a full-dimensional polytope in `ℝ³`,
the number of vertices plus the number of two-dimensional faces minus
the number of edges is two.
-/
theorem euler_relation (p : Set Point)
    (hpolytope : IsPolytope p)
    (hfullDimensional : AffineDimensionEq p 3) :
    ((facesOfDimension p 0).ncard + (facesOfDimension p 2).ncard) -
        (facesOfDimension p 1).ncard =
      2 := sorry

end

end Theorems100.PolyhedronFormula
