-- Statement-only formalization of "The Isoperimetric Theorem" from Hundred Theorems item 043.
-- It states the sharp area bound for rectifiable simple closed plane curves and characterizes
-- equality by circular images. This file contains no proof.

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Data.Real.Sqrt

noncomputable section

open Set
open scoped BigOperators

@[expose] public section

namespace Theorems100.IsoperimetricTheorem

abbrev Plane := ℝ × ℝ

def euclideanDist (z w : Plane) : ℝ :=
  Real.sqrt ((z.1 - w.1) ^ 2 + (z.2 - w.2) ^ 2)

def euclideanSphere (center : Plane) (radius : ℝ) : Set Plane :=
  {z | euclideanDist z center = radius}

def circlePi : ℝ :=
  4 * ∑' n : ℕ,
    (1 / (4 * (n : ℝ) + 1) - 1 / (4 * (n : ℝ) + 3))

def pathImage (g : ℝ → Plane) : Set Plane :=
  g '' Icc (0 : ℝ) 1

def IsSimplePath (g : ℝ → Plane) : Prop :=
  ContinuousOn g (Icc (0 : ℝ) 1) ∧
    ∀ ⦃s t : ℝ⦄, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → g s = g t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)

structure UnitIntervalPartition where
  segments : ℕ
  segments_pos : 0 < segments
  point : Fin (segments + 1) → ℝ
  point_strictMono : StrictMono point
  left_endpoint : point 0 = 0
  right_endpoint : point (Fin.last segments) = 1

def polygonalLength (g : ℝ → Plane) (p : UnitIntervalPartition) : ℝ :=
  ∑ i : Fin p.segments,
    euclideanDist (g (p.point i.castSucc)) (g (p.point i.succ))

def IsRectifiable (g : ℝ → Plane) : Prop :=
  BddAbove (Set.range (polygonalLength g))

noncomputable def pathLength (g : ℝ → Plane) : ℝ :=
  sSup (Set.range (polygonalLength g))

def IsBoundedPlaneSet (s : Set Plane) : Prop :=
  ∃ R : ℝ, ∀ z ∈ s, ‖z‖ ≤ R

def curveInside (g : ℝ → Plane) : Set Plane :=
  {z | z ∈ (pathImage g)ᶜ ∧
    IsBoundedPlaneSet (connectedComponentIn (pathImage g)ᶜ z)}

structure RectangleCover (s : Set Plane) where
  lower : ℕ → Plane
  upper : ℕ → Plane
  covers :
    ∀ z ∈ s, ∃ n : ℕ,
      (lower n).1 ≤ z.1 ∧ z.1 ≤ (upper n).1 ∧
      (lower n).2 ≤ z.2 ∧ z.2 ≤ (upper n).2

def rectangleArea (lower upper : Plane) : ENNReal :=
  ENNReal.ofReal ((upper.1 - lower.1) * (upper.2 - lower.2))

noncomputable def coverArea {s : Set Plane} (cover : RectangleCover s) : ENNReal :=
  ∑' n : ℕ, rectangleArea (cover.lower n) (cover.upper n)

noncomputable def planarOuterArea (s : Set Plane) : ENNReal :=
  ⨅ cover : RectangleCover s, coverArea cover

noncomputable def enclosedArea (g : ℝ → Plane) : ℝ :=
  (planarOuterArea (curveInside g)).toReal

theorem isoperimetric_theorem
    (L : ℝ) (g : ℝ → Plane)
    (hg_rectifiable : IsRectifiable g)
    (hg_simple : IsSimplePath g)
    (hg_closed : g 1 = g 0)
    (h_length : pathLength g = L) :
    enclosedArea g ≤ L ^ 2 / (4 * circlePi) ∧
      (enclosedArea g = L ^ 2 / (4 * circlePi) →
        ∃ center : Plane, ∃ radius : ℝ,
          pathImage g = euclideanSphere center radius) := sorry

end Theorems100.IsoperimetricTheorem
