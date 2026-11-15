-- Statement-only formalization of Thousand Theorems artifact Q193878
-- (thousand-theorems__lean4__Q193878), "Chinese remainder theorem": a finite
-- family of pairwise coprime ideals in a commutative ring yields a ring equivalence
-- between the quotient by their infimum and the product of their quotients.
-- This file contains no proof.

module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.Algebra.Ring.Fin
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic

@[expose] public section

namespace Q193878

open Function

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]

/-- The Chinese remainder theorem for a finite pairwise coprime family of ideals. -/
noncomputable def quotientInfRingEquivPiQuotient_statement (f : ι → Ideal R)
    (hf : Pairwise (IsCoprime on f)) : (R ⧸ ⨅ i, f i) ≃+* ∀ i, R ⧸ f i := sorry

end Q193878
