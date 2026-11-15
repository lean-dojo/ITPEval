-- Statement-only formalization of Thousand Theorems artifact Q656645
-- (thousand-theorems__lean4__Q656645), "Hilbert's basis theorem": the
-- univariate polynomial ring over a commutative Noetherian ring is itself
-- Noetherian. This file contains no proof.

module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

namespace Q656645

universe u

variable {R : Type u} [CommRing R]

/-- A polynomial ring over a Noetherian ring is Noetherian. -/
theorem hilbert_basis_theorem_statement [IsNoetherianRing R] :
    IsNoetherianRing (Polynomial R) := sorry

end Q656645
