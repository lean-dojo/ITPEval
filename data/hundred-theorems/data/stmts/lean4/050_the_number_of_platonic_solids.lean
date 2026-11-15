-- Statement-only formalization of "The Number of Platonic Solids" from Hundred Theorems item 050.
-- It classifies the constant face-edge and vertex-edge incidence counts of full-dimensional
-- polytopes in real three-space, with exactly the five Platonic pairs. This file contains no proof.

module

public import Mathlib.Data.Real.Sqrt
public import Mathlib.Data.Set.Card

@[expose] public section

open scoped BigOperators

namespace Theorems100.NumberOfPlatonicSolids

noncomputable section

abbrev Point := Fin 3 → ℝ

/-- The affine combination of a finite family of points with the given coefficients. -/
def weightedPoint {k : ℕ} (coefficients : Fin k → ℝ) (points : Fin k → Point) : Point :=
  fun coordinate => ∑ i, coefficients i * points i coordinate

/-- The convex hull of a finite indexed family of points. -/
def finiteConvexHull {k : ℕ} (vertices : Fin k → Point) : Set Point :=
  {x |
    ∃ coefficients : Fin k → ℝ,
      (∀ i, 0 ≤ coefficients i) ∧
        (∑ i, coefficients i) = 1 ∧
          x = weightedPoint coefficients vertices}

/-- A polytope is the convex hull of finitely many points. -/
def IsPolytope (p : Set Point) : Prop :=
  ∃ k : ℕ, ∃ vertices : Fin k → Point, p = finiteConvexHull vertices

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
def AffineIndependent {k : ℕ} (points : Fin k → Point) : Prop :=
  ∀ coefficients : Fin k → ℝ,
    (∑ i, coefficients i) = 0 →
      (∀ coordinate : Fin 3, (∑ i, coefficients i * points i coordinate) = 0) →
        ∀ i, coefficients i = 0

/-- The set has affine dimension exactly `d`. -/
def AffineDimensionEq (s : Set Point) (d : ℕ) : Prop :=
  (∃ points : Fin (d + 1) → Point,
      (∀ i, points i ∈ s) ∧ AffineIndependent points) ∧
    ¬∃ points : Fin (d + 2) → Point,
      (∀ i, points i ∈ s) ∧ AffineIndependent points

/--
A full-dimensional polytope in real three-space has a constant number `m` of edges
on each two-dimensional face and a constant number `n` of edges at each vertex if
and only if `(m, n)` is one of the five Platonic incidence pairs.
-/
theorem number_of_platonic_solids (m n : ℕ) :
    (∃ p : Set Point,
        IsPolytope p ∧
          AffineDimensionEq p 3 ∧
            (∀ f : Set Point,
              IsFace f p ∧ AffineDimensionEq f 2 →
                {e : Set Point |
                    IsFace e p ∧ AffineDimensionEq e 1 ∧ e ⊆ f}.ncard =
                  m) ∧
              (∀ v : Set Point,
                IsFace v p ∧ AffineDimensionEq v 0 →
                  {e : Set Point |
                      IsFace e p ∧ AffineDimensionEq e 1 ∧ v ⊆ e}.ncard =
                    n)) ↔
      (m = 3 ∧ n = 3) ∨
        (m = 4 ∧ n = 3) ∨
          (m = 3 ∧ n = 4) ∨
            (m = 5 ∧ n = 3) ∨
              (m = 3 ∧ n = 5) := sorry

end

end Theorems100.NumberOfPlatonicSolids
