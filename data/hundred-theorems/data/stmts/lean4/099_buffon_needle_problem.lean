/-
Copyright (c) 2024 Enrico Z. Borba. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Z. Borba
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Density
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Notation

/-!

# Freek № 99: Buffon's Needle

This file proves Theorem 99 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/), also
known as Buffon's Needle, which gives the probability of a needle of length `l > 0` crossing any
one of infinite vertical lines spaced out `d > 0` apart.

The two cases are proven in `buffon_short` and `buffon_long`.

## Overview of the Proof

We define a random variable `B : Ω → ℝ × ℝ` with a uniform distribution on `[-d/2, d/2] × [0, π]`.
This represents the needle's x-position and angle with respect to a vertical line. By symmetry, we
need to consider only a single vertical line positioned at `x = 0`. A needle therefore crosses the
vertical line if its projection onto the x-axis contains `0`.

We define a random variable `N : Ω → ℝ` that is `1` if the needle crosses a vertical line, and `0`
otherwise. This is defined as `fun ω => Set.indicator (needleProjX l (B ω).1 (B ω).2) 1 0`.
f
As in many references, the problem is split into two cases, `l ≤ d` (`buffon_short`), and `d ≤ l`
(`buffon_long`). For both cases, we show that
```lean
ℙ[N] = (d * π) ⁻¹ *
    ∫ θ in 0..π,
      ∫ x in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1
```
In the short case `l ≤ d`, we show that `[-l * θ.sin/2, l * θ.sin/2] ⊆ [-d/2, d/2]`
(`short_needle_inter_eq`), and therefore the inner integral simplifies to
```lean
∫ x in (-θ.sin * l / 2)..(θ.sin * l / 2), 1 = θ.sin * l
```
Which then concludes in the short case being `ℙ[N] = (2 * l) / (d * π)`.

In the long case, `l ≤ d` (`buffon_long`), we show the outer integral simplifies to
```lean
∫ θ in 0..π, min d (θ.sin * l)
```
which can be expanded to
```lean
2 * (
  ∫ θ in 0..(d / l).arcsin, min d (θ.sin * l) +
  ∫ θ in (d / l).arcsin..(π / 2), min d (θ.sin * l)
)
```
We then show the two integrals equal their respective values `l - √(l^2 - d^2)` and
`(π / 2 - (d / l).arcsin) * d`. Then with some algebra we conclude
```lean
ℙ[N] = (2 * l) / (d * π) - 2 / (d * π) * (√(l^2 - d^2) + d * (d / l).arcsin) + 1
```

## References

* https://en.wikipedia.org/wiki/Buffon%27s_needle_problem
* https://www.math.leidenuniv.nl/~hfinkeln/seminarium/stelling_van_Buffon.pdf
* https://www.isa-afp.org/entries/Buffons_Needle.html

-/

open MeasureTheory (MeasureSpace IsProbabilityMeasure Measure pdf.IsUniform)
open ProbabilityTheory Real

namespace BuffonsNeedle

variable
  /- Probability theory variables. -/
  {Ω : Type*} [MeasureSpace Ω]
  /- Buffon's needle variables. -/
  /-
    - `d > 0` is the distance between parallel lines.
    - `l > 0` is the length of the needle.
  -/
  (d l : ℝ)
  (hd : 0 < d)
  (hl : 0 < l)
  /- `B = (X, Θ)` is the joint random variable for the x-position and angle of the needle. -/
  (B : Ω → ℝ × ℝ)
  (hBₘ : Measurable B)
  /- `B` is uniformly distributed on `[-d/2, d/2] × [0, π]`. -/
  (hB : pdf.IsUniform B ((Set.Icc (-d / 2) (d / 2)) ×ˢ (Set.Icc 0 π)) ℙ)

/--
Projection of a needle onto the x-axis. The needle's center is at x-coordinate `x`, of length
`l` and angle `θ`. Note, `θ` is measured relative to the y-axis, that is, a vertical needle has
`θ = 0`.
-/
def needleProjX (x θ : ℝ) : Set ℝ := Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)

/--
The indicator function of whether a needle at position `⟨x, θ⟩ : ℝ × ℝ` crosses the line `x = 0`.

In order to faithfully model the problem, we compose `needleCrossesIndicator` with a random
variable `B : Ω → ℝ × ℝ` with uniform distribution on `[-d/2, d/2] × [0, π]`. Then, by symmetry,
the probability that the needle crosses `x = 0`, is the same as the probability of a needle
crossing any of the infinitely spaced vertical lines distance `d` apart.
-/
noncomputable def needleCrossesIndicator (p : ℝ × ℝ) : ℝ :=
  Set.indicator (needleProjX l p.1 p.2) 1 0

/--
A random variable representing whether the needle crosses a line.

The line is at `x = 0`, and therefore a needle crosses the line if its projection onto the x-axis
contains `0`. This random variable is `1` if the needle crosses the line, and `0` otherwise.
-/
noncomputable def N : Ω → ℝ := needleCrossesIndicator l ∘ B

/--
The possible x-positions and angle relative to the y-axis of a needle.
-/
abbrev needleSpace : Set (ℝ × ℝ) := Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π

include hd in
lemma volume_needleSpace : ℙ (needleSpace d) = ENNReal.ofReal (d * π) := by sorry
lemma measurable_needleCrossesIndicator : Measurable (needleCrossesIndicator l) := by sorry
lemma stronglyMeasurable_needleCrossesIndicator :
    MeasureTheory.StronglyMeasurable (needleCrossesIndicator l) := by sorry
lemma integrable_needleCrossesIndicator :
    MeasureTheory.Integrable (needleCrossesIndicator l)
      (Measure.prod
        (Measure.restrict ℙ (Set.Icc (-d / 2) (d / 2)))
        (Measure.restrict ℙ (Set.Icc 0 π))) := by sorry
lemma buffon_integral :
    𝔼[N l B] = (d * π)⁻¹ *
      ∫ (θ : ℝ) in Set.Icc 0 π,
      ∫ (_ : ℝ) in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1 := by sorry
lemma short_needle_inter_eq (h : l ≤ d) (θ : ℝ) :
    Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2) =
    Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2) := by sorry
theorem buffon_short (h : l ≤ d) : ℙ[N l B] = (2 * l) * (d * π)⁻¹ := by sorry
lemma intervalIntegrable_min_const_sin_mul (a b : ℝ) :
    IntervalIntegrable (fun (θ : ℝ) => min d (θ.sin * l)) ℙ a b := by sorry
lemma integral_min_eq_two_mul :
    ∫ θ in 0..π, min d (θ.sin * l) = 2 * ∫ θ in 0..π / 2, min d (θ.sin * l) := by sorry
lemma integral_zero_to_arcsin_min :
    ∫ θ in 0..(d / l).arcsin, min d (θ.sin * l) = (1 - √(1 - (d / l) ^ 2)) * l := by sorry
lemma integral_arcsin_to_pi_div_two_min (h : d ≤ l) :
    ∫ θ in (d / l).arcsin..(π / 2), min d (θ.sin * l) = (π / 2 - (d / l).arcsin) * d := by sorry
theorem buffon_long (h : d ≤ l) :
    ℙ[N l B] = (2 * l) / (d * π) - 2 / (d * π) * (√(l ^ 2 - d ^ 2) + d * (d / l).arcsin) + 1 := by sorry
end BuffonsNeedle
