-- Statement-only formalization of Thousand Theorems artifact Q1186808
-- (thousand-theorems__lean4__Q1186808), "Lucas's theorem": for a prime `p`,
-- a binomial coefficient is congruent modulo `p` to the product of the
-- binomial coefficients of its base-`p` digits. This file contains no proof.

module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

open Finset hiding choose

open Nat

namespace Choose

variable {n k p : ℕ} [Fact p.Prime]

/-- Lucas's theorem for natural-number binomial coefficients, stated as an integer congruence. -/
theorem lucas_theorem {a : ℕ} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a) :
    choose n k ≡ ∏ i ∈ range a, choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p] := sorry

end Choose
