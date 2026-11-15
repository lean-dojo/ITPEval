/-
Copyright (c) 2021 Matt Kempster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Kempster
-/
import Mathlib.Geometry.Euclidean.Triangle

/-!
# Freek № 57: Heron's Formula

This file proves Theorem 57 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/),
also known as Heron's formula, which gives the area of a triangle based only on its three sides'
lengths.

## References

* https://en.wikipedia.org/wiki/Herons_formula

-/


open Real EuclideanGeometry

open scoped Real EuclideanGeometry

namespace Theorems100

local notation "√" => Real.sqrt

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Heron's formula**: The area of a triangle with side lengths `a`, `b`, and `c` is
  `√(s * (s - a) * (s - b) * (s - c))` where `s = (a + b + c) / 2` is the semiperimeter.
  We show this by equating this formula to `a * b * sin γ`, where `γ` is the angle opposite
  the side `c`.
-/
theorem heron {p₁ p₂ p₃ : P} (h1 : p₁ ≠ p₂) (h2 : p₃ ≠ p₂) :
    let a := dist p₁ p₂
    let b := dist p₃ p₂
    let c := dist p₁ p₃
    let s := (a + b + c) / 2
    1 / 2 * a * b * sin (∠ p₁ p₂ p₃) = √(s * (s - a) * (s - b) * (s - c)) := by sorry
end Theorems100
