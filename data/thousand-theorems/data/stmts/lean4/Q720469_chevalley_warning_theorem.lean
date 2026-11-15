-- Statement-only formalization of Thousand Theorems artifact Q720469
-- (thousand-theorems__lean4__Q720469), "Chevalley–Warning theorem": over a
-- finite field of characteristic p, the characteristic divides the number of
-- common zeros of a finite polynomial family when the sum of total degrees is
-- less than the number of variables. This file contains no proof.

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees

@[expose] public section

namespace Q720469

open Finset MvPolynomial

variable {K σ ι : Type*} [Fintype K] [Field K] [Fintype σ] [DecidableEq σ]
variable [DecidableEq K] (p : ℕ) [CharP K p]

/-- The finitary Chevalley–Warning theorem for a family of multivariate polynomials. -/
theorem char_dvd_card_solutions_of_sum_lt_statement
    {s : Finset ι} {f : ι → MvPolynomial σ K}
    (h : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // ∀ i ∈ s, eval x (f i) = 0 } := sorry

end Q720469
