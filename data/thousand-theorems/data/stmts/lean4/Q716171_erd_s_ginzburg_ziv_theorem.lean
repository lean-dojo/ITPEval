-- Statement-only formalization of Thousand Theorems artifact Q716171
-- (thousand-theorems__lean4__Q716171), "Erdős–Ginzburg–Ziv theorem": any
-- sequence of at least 2 * n - 1 elements of ZMod n has an n-element
-- subsequence whose sum is zero. This file contains no proof.

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic

public section

open Finset

namespace Q716171

variable {ι : Type*} {n : ℕ} {s : Finset ι}

/-- The Erdős–Ginzburg–Ziv theorem for finite indexed sequences in `ZMod n`. -/
theorem erdos_ginzburg_ziv (a : ι → ZMod n) (hs : 2 * n - 1 ≤ #s) :
    ∃ t ⊆ s, #t = n ∧ ∑ i ∈ t, a i = 0 := sorry

end Q716171
