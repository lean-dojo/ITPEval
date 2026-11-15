-- Statement-only formalization of Thousand Theorems artifact Q172298
-- (thousand-theorems__lean4__Q172298), "Lasker–Noether theorem": a finite primary
-- decomposition of a submodule can be regrouped so that the radicals of its colon
-- ideals are pairwise distinct. This file contains no proof.

module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Order.Irreducible
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

@[expose] public section

open Ideal

open scoped Function

namespace Q172298

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A primary decomposition can be regrouped to have pairwise distinct colon radicals. -/
theorem isPrimary_decomposition_pairwise_ne_radical_statement
    {N : Submodule R M} {s : Finset (Submodule R M)}
    (hs : s.inf id = N) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Submodule R M), t.inf id = N ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      (t : Set (Submodule R M)).Pairwise
        ((· ≠ ·) on fun J ↦ (J.colon Set.univ).radical) := sorry

end Q172298
