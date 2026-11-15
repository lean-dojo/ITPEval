-- Statement-only formalization of Thousand Theorems artifact Q472883
-- (thousand-theorems__lean4__Q472883), "Quadratic reciprocity theorem": Legendre
-- symbols of distinct odd primes, and Jacobi symbols of odd natural numbers, obey
-- the quadratic reciprocity sign law. This file contains no proof.

module

public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace Q472883

/-- The Legendre symbol on a prime modulus, encoded by zero and square status. -/
noncomputable def legendreSymbol (p : ℕ) (a : ℤ) : ℤ :=
  if (a : ZMod p) = 0 then 0
  else @ite ℤ (IsSquare (a : ZMod p)) (Classical.propDecidable _) 1 (-1)

/-- The Jacobi symbol as the product over the prime factorization, with multiplicity. -/
noncomputable def jacobiSymbol (a : ℤ) (b : ℕ) : ℤ :=
  (b.primeFactorsList.map fun p ↦ legendreSymbol p a).prod

/-- Quadratic reciprocity for Legendre symbols of distinct odd primes. -/
theorem legendre_quadratic_reciprocity_statement {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSymbol q p * legendreSymbol p q = (-1) ^ (p / 2 * (q / 2)) := sorry

/-- Quadratic reciprocity for Jacobi symbols of odd natural numbers. -/
theorem jacobi_quadratic_reciprocity_statement {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    jacobiSymbol a b = (-1) ^ (a / 2 * (b / 2)) * jacobiSymbol b a := sorry

end Q472883
