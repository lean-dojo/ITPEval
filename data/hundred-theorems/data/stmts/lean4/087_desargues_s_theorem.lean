-- Statement-only formalization of "Desargues's Theorem" from Hundred Theorems item 087.
-- In the real projective plane, corresponding sides of two perspective triangles meet in
-- three collinear points, under the source's explicit nondegeneracy conditions.
-- This file contains no proof.

import Mathlib.Data.Real.Basic

namespace Theorems100.Desargues

/-- A projective-plane point represented by nonzero homogeneous coordinates in `Real ^ 3`. -/
abbrev ProjectivePoint := {v : Fin 3 → ℝ // v ≠ 0}

/--
Three projective points are collinear exactly when their homogeneous coordinate vectors
are linearly dependent.
-/
def Collinear (a b c : ProjectivePoint) : Prop :=
  ∃ x y z : ℝ,
    (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      ∀ i, x * a.1 i + y * b.1 i + z * c.1 i = 0

/--
Desargues's theorem in the explicit incidence configuration used by the HOL Light source.
The triangles `A A'`, `B B'`, and `C C'` are perspective from `P`; `Q`, `R`, and `S`
are the intersections of corresponding sides.
-/
theorem desargues
    (A A' B B' C C' P Q R S : ProjectivePoint)
    (h_nondegenerate :
      ¬Collinear A' B S ∧
      ¬Collinear A P C ∧
      ¬Collinear A P R ∧
      ¬Collinear A C B ∧
      ¬Collinear A B R ∧
      ¬Collinear C' P A' ∧
      ¬Collinear C' P B ∧
      ¬Collinear C' P B' ∧
      ¬Collinear C' A' S ∧
      ¬Collinear C' A' B' ∧
      ¬Collinear P C A' ∧
      ¬Collinear P C B ∧
      ¬Collinear P A' R ∧
      ¬Collinear P B Q ∧
      ¬Collinear P Q B' ∧
      ¬Collinear C B S ∧
      ¬Collinear A' Q B')
    (h_incidence :
      Collinear P A' A ∧
      Collinear P B B' ∧
      Collinear P C' C ∧
      Collinear B C Q ∧
      Collinear B' C' Q ∧
      Collinear A R C ∧
      Collinear A' C' R ∧
      Collinear B S A ∧
      Collinear A' S B') :
    Collinear Q S R := sorry

end Theorems100.Desargues
