-- Statement-only formalization of Thousand Theorems artifact Q6783821
-- (thousand-theorems__lean4__Q6783821), "Mason–Stothers theorem": for three
-- nonzero polynomials over a field whose first two are coprime and whose sum is
-- zero, their degrees are bounded by the radical of their product unless all
-- three derivatives vanish. This file contains no proof.

module

public import Mathlib.RingTheory.Polynomial.Radical

@[expose] public section

open Polynomial UniqueFactorizationMonoid

namespace Q6783821

variable {k : Type*} [Field k] [DecidableEq k]

/-- The polynomial ABC theorem, also known as the Mason–Stothers theorem. -/
theorem mason_stothers_theorem
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0) :
    (natDegree a + 1 ≤ (radical (a * b * c)).natDegree ∧
      natDegree b + 1 ≤ (radical (a * b * c)).natDegree ∧
      natDegree c + 1 ≤ (radical (a * b * c)).natDegree) ∨
      derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0 := sorry

end Q6783821
