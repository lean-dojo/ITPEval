-- Statement-only formalization of Thousand Theorems artifact Q3527241
-- (thousand-theorems__lean4__Q3527241), "Krull's principal ideal theorem":
-- in a commutative Noetherian ring, every prime ideal minimal over a principal
-- ideal has height at most one. This file contains no proof.

module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.IsPrincipal
public import Mathlib.RingTheory.Noetherian.Basic

namespace Q3527241

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- A prime ideal minimal over a principal ideal has height at most one. -/
theorem krulls_principal_ideal_theorem_statement
    (I : Ideal R) [I.IsPrincipal] (p : Ideal R)
    (hp : p ∈ I.minimalPrimes) : p.height ≤ 1 := sorry

end Q3527241
