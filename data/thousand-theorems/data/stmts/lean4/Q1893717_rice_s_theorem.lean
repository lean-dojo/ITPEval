-- Statement-only formalization of Thousand Theorems artifact Q1893717
-- (thousand-theorems__lean4__Q1893717), "Rice's theorem": a computable
-- semantic property of partial-recursive functions that holds for one such
-- function holds for every partial-recursive function. This file contains no proof.

module

public import Mathlib.Computability.Halting

@[expose] public section

namespace Q1893717

/-- Rice's theorem for computable properties of partial-recursive functions. -/
theorem rice_statement (C : Set (ℕ →. ℕ))
    (h : ComputablePred fun c => Nat.Partrec.Code.eval c ∈ C) {f g : ℕ →. ℕ}
    (hf : Nat.Partrec f) (hg : Nat.Partrec g) (fC : f ∈ C) :
    g ∈ C := sorry

end Q1893717
