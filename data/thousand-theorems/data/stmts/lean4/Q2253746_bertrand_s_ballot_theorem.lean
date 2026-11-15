-- Statement-only formalization of Thousand Theorems artifact Q2253746
-- (thousand-theorems__lean4__Q2253746), "Bertrand's ballot theorem": when one
-- candidate receives more votes than another, the probability that the leading
-- candidate stays strictly ahead throughout the count is their vote-count difference
-- divided by the total number of votes. This file contains no proof.

module

public import Mathlib.Probability.UniformOn

@[expose] public section

open Set ProbabilityTheory MeasureTheory

open scoped ENNReal

namespace Q2253746

/-- Lists whose every nonempty suffix has positive integer sum. -/
def staysPositive : Set (List ℤ) :=
  {l | ∀ l₂, l₂ ≠ [] → l₂ <:+ l → 0 < l₂.sum}

/-- Vote lists with exactly `p` entries equal to `1` and `q` entries equal to `-1`. -/
def countedSequence (p q : ℕ) : Set (List ℤ) :=
  {l | l.count 1 = p ∧ l.count (-1) = q ∧ ∀ x ∈ l, x = (1 : ℤ) ∨ x = -1}

/-- Bertrand's ballot theorem for uniformly distributed vote-counting sequences. -/
theorem ballot_problem :
    letI : MeasurableSpace (List ℤ) := ⊤
    ∀ q p, q < p →
      uniformOn (countedSequence p q) staysPositive = (p - q) / (p + q) := sorry

end Q2253746
