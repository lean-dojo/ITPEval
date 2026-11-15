-- Statement-only formalization of Thousand Theorems artifact Q1566341
-- (thousand-theorems__lean4__Q1566341), "Hindman's theorem": in any finite
-- cover of the finite-products set of a stream in a semigroup, one member
-- contains the finite-products set of another stream. This file contains no proof.

module

public import Mathlib.Combinatorics.Hindman

@[expose] public section

namespace Q1566341

/-- The strong finite-products form of Hindman's theorem. -/
theorem hindman_fp_partition_regular_statement {M} [Semigroup M] (a : Stream' M)
    (s : Set (Set M)) (sfin : s.Finite) (scov : Hindman.FP a ⊆ ⋃₀ s) :
    ∃ c ∈ s, ∃ b : Stream' M, Hindman.FP b ⊆ c := sorry

end Q1566341
