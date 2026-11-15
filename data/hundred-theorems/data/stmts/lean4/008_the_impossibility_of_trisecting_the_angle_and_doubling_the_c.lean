-- Statement-only formalization of "The Impossibility of Trisecting the Angle and Doubling the
-- Cube" from Hundred Theorems item 008. This file contains no proof.

module

public import Mathlib.Data.Real.Sqrt

@[expose] public section

/-!
# The Impossibility of Trisecting the Angle and Doubling the Cube

This file models planar straightedge-and-compass constructions from rational points. It records
that constructible coordinates lie in the closure of the rationals under field operations and
nonnegative square roots, and states the classical impossibility results for doubling the cube and
trisecting a 60-degree angle.
-/

namespace Theorems100.ImpossibleGeometry

noncomputable section

abbrev Point := ℝ × ℝ

/-- A real number represented by a rational number. -/
def IsRational (x : ℝ) : Prop :=
  ∃ q : ℚ, (q : ℝ) = x

/-- Reals obtainable from rational numbers using field operations and nonnegative square roots. -/
inductive Radical : ℝ → Prop where
  | rational {x : ℝ} : IsRational x → Radical x
  | neg {x : ℝ} : Radical x → Radical (-x)
  | inv {x : ℝ} : Radical x → x ≠ 0 → Radical x⁻¹
  | add {x y : ℝ} : Radical x → Radical y → Radical (x + y)
  | mul {x y : ℝ} : Radical x → Radical y → Radical (x * y)
  | sqrt {x : ℝ} : Radical x → 0 ≤ x → Radical (Real.sqrt x)

/-- Euclidean distance between two points in the plane. -/
def distance (a b : Point) : ℝ :=
  Real.sqrt ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2)

/-- The lines through `a, b` and `c, d` are parallel. -/
def Parallel (a b c d : Point) : Prop :=
  (a.1 - b.1) * (c.2 - d.2) = (a.2 - b.2) * (c.1 - d.1)

/-- Three planar points are collinear. -/
def Collinear (a p b : Point) : Prop :=
  Parallel a p a b

/-- `p` lies on both lines determined by `a, b` and `c, d`. -/
def IsIntersection (p a b c d : Point) : Prop :=
  Collinear a p b ∧ Collinear c p d

/-- Points obtainable from rational points by line-line, line-circle, and circle-circle
intersections. -/
inductive Constructible : Point → Prop where
  | rational {p : Point} :
      IsRational p.1 → IsRational p.2 → Constructible p
  | lineLine {a b c d p : Point} :
      Constructible a →
      Constructible b →
      Constructible c →
      Constructible d →
      ¬Parallel a b c d →
      IsIntersection p a b c d →
      Constructible p
  | lineCircle {a b c d e p : Point} :
      Constructible a →
      Constructible b →
      Constructible c →
      Constructible d →
      Constructible e →
      a ≠ b →
      Collinear a p b →
      distance c p = distance d e →
      Constructible p
  | circleCircle {a b c d e f p : Point} :
      Constructible a →
      Constructible b →
      Constructible c →
      Constructible d →
      Constructible e →
      Constructible f →
      ¬(a = d ∧ distance b c = distance e f) →
      distance a p = distance b c →
      distance d p = distance e f →
      Constructible p

/-- A monic cubic with rational coefficients that has a radical root has a rational root. -/
theorem cubic_root_rational {a b c : ℝ}
    (ha : IsRational a) (hb : IsRational b) (hc : IsRational c) :
    (∃ x : ℝ, Radical x ∧ x ^ 3 + a * x ^ 2 + b * x + c = 0) →
      ∃ x : ℝ, IsRational x ∧ x ^ 3 + a * x ^ 2 + b * x + c = 0 := by sorry

/-- Both coordinates of a constructible point are square-root radicals. -/
theorem constructible_coordinates_radical {p : Point} (hp : Constructible p) :
    Radical p.1 ∧ Radical p.2 := by sorry

/-- No square-root radical has cube equal to two. -/
theorem no_radical_cube_root_two :
    ¬∃ x : ℝ, Radical x ∧ x ^ 3 = 2 := by sorry

/-- The cubic equation arising from trisecting a 60-degree angle has no radical root. -/
theorem no_radical_trisection_polynomial :
    ¬∃ x : ℝ, Radical x ∧ x ^ 3 - 3 * x - 1 = 0 := by sorry

/-- Algebraic characterization of `cos (π / 9)`: the positive root in `(0, 1)` of the
triple-angle cubic. -/
def IsCosPiOverNine (x : ℝ) : Prop :=
  0 < x ∧ x < 1 ∧ 8 * x ^ 3 - 6 * x - 1 = 0

/-- A segment whose length is the cube root of two is not constructible. -/
theorem impossibility_of_doubling_the_cube {x : ℝ} (hx : x ^ 3 = 2) :
    ¬Constructible (x, 0) := by sorry

/-- The point encoding the trisection of a 60-degree angle is not constructible. The abscissa is
presented by the exact algebraic characterization of `cos (π / 9)`. -/
theorem impossibility_of_trisecting_angle_pi_over_3 {x : ℝ} (hx : IsCosPiOverNine x) :
    ¬Constructible (x, 0) := by sorry

/-- No constructible point has the algebraically characterized `cos (π / 9)` as its first
coordinate. -/
theorem impossibility_of_trisecting_angle_pi_over_3_for_any_ordinate
    {x : ℝ} (hx : IsCosPiOverNine x) (y : ℝ) :
    ¬Constructible (x, y) := by sorry

end

end Theorems100.ImpossibleGeometry
