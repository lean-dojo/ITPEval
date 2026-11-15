-- Statement-only formalization of Thousand Theorems artifact Q7888360
-- (thousand-theorems__lean4__Q7888360), "Structure theorem for finitely generated
-- modules over a principal ideal domain": every finitely generated module over a
-- PID is a product of a finite-rank free module and a finite direct sum of cyclic
-- quotients by powers of irreducible elements.
-- This file contains no proof.

module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

universe u v

namespace Q7888360

open scoped DirectSum

variable (R : Type u) [CommRing R] [IsPrincipalIdealRing R] [IsDomain R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The structure theorem for finitely generated modules over a principal ideal domain. -/
theorem equiv_free_prod_directSum_statement [Module.Finite R M] :
    ∃ (n : ℕ) (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i)
      (e : ι → ℕ), Nonempty <| M ≃ₗ[R] (Fin n →₀ R) × ⨁ i : ι, R ⧸ R ∙ p i ^ e i := sorry

end Q7888360
