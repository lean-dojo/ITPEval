/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jujian Zhang
-/
module

public import Mathlib.Algebra.Polynomial.DenomsClearable
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Order.Interval.Set.Group

/-!

# Liouville's theorem

This file contains a proof of Liouville's theorem stating that all Liouville numbers are
transcendental.

To obtain this result, there is first a proof that Liouville numbers are irrational and two
technical lemmas.  These lemmas exploit the fact that a polynomial with integer coefficients
takes integer values at integers.  When evaluating at a rational number, we can clear denominators
and obtain precise inequalities that ultimately allow us to prove transcendence of
Liouville numbers.
-/

@[expose] public section


/-- A Liouville number is a real number `x` such that for every natural number `n`, there exist
`a, b ∈ ℤ` with `1 < b` such that `0 < |x - a/b| < 1/bⁿ`.
In the implementation, the condition `x ≠ a/b` replaces the traditional equivalent `0 < |x - a/b|`.
-/
def Liouville (x : ℝ) :=
  ∀ n : ℕ, ∃ a b : ℤ, 1 < b ∧ x ≠ a / b ∧ |x - a / b| < 1 / (b : ℝ) ^ n

namespace Liouville

protected theorem irrational {x : ℝ} (h : Liouville x) : Irrational x := by sorry
open Polynomial Metric Set Real RingHom

open scoped Polynomial

/-- Let `Z, N` be types, let `R` be a metric space, let `α : R` be a point and let
`j : Z → N → R` be a function.  We aim to estimate how close we can get to `α`, while staying
in the image of `j`.  The points `j z a` of `R` in the image of `j` come with a "cost" equal to
`d a`.  As we get closer to `α` while staying in the image of `j`, we are interested in bounding
the quantity `d a * dist α (j z a)` from below by a strictly positive amount `1 / A`: the intuition
is that approximating well `α` with the points in the image of `j` should come at a high cost.  The
hypotheses on the function `f : R → R` provide us with sufficient conditions to ensure our goal.
The first hypothesis is that `f` is Lipschitz at `α`: this yields a bound on the distance.
The second hypothesis is specific to the Liouville argument and provides the missing bound
involving the cost function `d`.

This lemma collects the properties used in the proof of `exists_pos_real_of_irrational_root`.
It is stated in more general form than needed: in the intended application, `Z = ℤ`, `N = ℕ`,
`R = ℝ`, `d a = (a + 1) ^ f.nat_degree`, `j z a = z / (a + 1)`, `f ∈ ℤ[x]`, `α` is an irrational
root of `f`, `ε` is small, `M` is a bound on the Lipschitz constant of `f` near `α`, `n` is
the degree of the polynomial `f`.
-/
theorem exists_one_le_pow_mul_dist {Z N R : Type*} [PseudoMetricSpace R] {d : N → ℝ}
    {j : Z → N → R} {f : R → R} {α : R} {ε M : ℝ}
    -- denominators are positive
    (d0 : ∀ a : N, 1 ≤ d a)
    (e0 : 0 < ε)
    -- function is Lipschitz at α
    (B : ∀ ⦃y : R⦄, y ∈ closedBall α ε → dist (f α) (f y) ≤ dist α y * M)
    -- clear denominators
    (L : ∀ ⦃z : Z⦄, ∀ ⦃a : N⦄, j z a ∈ closedBall α ε → 1 ≤ d a * dist (f α) (f (j z a))) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : Z, ∀ a : N, 1 ≤ d a * (dist α (j z a) * A) := by sorry
theorem exists_pos_real_of_irrational_root {α : ℝ} (ha : Irrational α) {f : ℤ[X]} (f0 : f ≠ 0)
    (fa : eval α (map (algebraMap ℤ ℝ) f) = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℤ, ∀ b : ℕ,
      (1 : ℝ) ≤ ((b : ℝ) + 1) ^ f.natDegree * (|α - a / (b + 1)| * A) := by sorry

/-- Liouville's theorem: every Liouville number is transcendental. -/
protected theorem transcendental {x : ℝ} (lx : Liouville x) : Transcendental ℤ x := by sorry

end Liouville
