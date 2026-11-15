/-
Copyright (c) 2022 John Nicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicol
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# Wilson's theorem.

This file contains a proof of Wilson's theorem.

The heavy lifting is mostly done by the previous `wilsons_lemma`,
but here we also prove the other logical direction.

This could be generalized to similar results about finite abelian groups.

## References

* [Wilson's Theorem](https://en.wikipedia.org/wiki/Wilson%27s_theorem)

## TODO

* Give `wilsons_lemma` a descriptive name.
-/

public section

assert_not_exists legendreSym.quadratic_reciprocity

open Finset Nat FiniteField ZMod

open scoped Nat

namespace ZMod

variable (p : ℕ) [Fact p.Prime]

/-- **Wilson's Lemma**: the product of `1`, ..., `p-1` is `-1` modulo `p`. -/
@[simp]
theorem wilsons_lemma : ((p - 1)! : ZMod p) = -1 := by sorry
theorem prod_Ico_one_prime : ∏ x ∈ Ico 1 p, (x : ZMod p) = -1 := by sorry
end ZMod

namespace Nat

variable {n : ℕ}

/-- For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` only if n is prime. -/
theorem prime_of_fac_equiv_neg_one (h : ((n - 1)! : ZMod n) = -1) (h1 : n ≠ 1) : Prime n := by sorry
theorem prime_iff_fac_equiv_neg_one (h : n ≠ 1) : Prime n ↔ ((n - 1)! : ZMod n) = -1 := by sorry
end Nat
