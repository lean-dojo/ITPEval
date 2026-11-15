-- Statement-only formalization of Thousand Theorems artifact Q3527118
-- (thousand-theorems__lean4__Q3527118), "Mahler's theorem": every continuous
-- function on the p-adic integers with values in a complete ultrametric normed
-- module is the sum of its Mahler series. This file contains no proof.

module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.ContinuousMap.Algebra

@[expose] public section

open IsUltrametricDist
open scoped fwdDiff

variable {p : ℕ} [hp : Fact p.Prime]

namespace Q3527118

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]

/--
Mahler's theorem, with the Mahler basis characterized as the continuous extension of the
natural-number binomial coefficient functions.
-/
theorem mahler_theorem_statement :
    ∃ b : ℕ → C(ℤ_[p], ℤ_[p]),
      (∀ k n : ℕ, b k (n : ℤ_[p]) = (n.choose k : ℤ_[p])) ∧
      ∀ f : C(ℤ_[p], E),
        HasSum
          (fun n ↦ b n • ContinuousMap.const ℤ_[p] (Δ_[1]^[n] f 0))
          f := sorry

end Q3527118
