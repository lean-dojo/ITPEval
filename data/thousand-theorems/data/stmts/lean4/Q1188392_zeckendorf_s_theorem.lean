-- Statement-only formalization of Thousand Theorems artifact Q1188392
-- (thousand-theorems__lean4__Q1188392), "Zeckendorf's theorem": every natural
-- number corresponds uniquely to a sum of distinct, non-consecutive Fibonacci
-- numbers, excluding the first two Fibonacci indices. This file contains no proof.

module

public import Mathlib.Data.Nat.Fib.Basic

@[expose] public section

namespace List

/-- A Zeckendorf representation is a list of pairwise non-consecutive Fibonacci indices
greater than or equal to two, ordered from greatest to least. -/
def IsZeckendorfRep (l : List ℕ) : Prop :=
  (l ++ [0]).IsChain (fun a b ↦ b + 2 ≤ a)

end List

namespace Nat

/-- Every natural number has a unique Zeckendorf representation whose Fibonacci sum is that
number. -/
theorem zeckendorfEquiv_statement (n : ℕ) :
    ∃! l : List ℕ, l.IsZeckendorfRep ∧ (l.map fib).sum = n := sorry

end Nat
