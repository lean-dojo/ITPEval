-- Statement-only formalization of Thousand Theorems artifact Q764287
-- (thousand-theorems__lean4__Q764287), "Van der Waerden's theorem": every finite
-- subset of a finitely colored additive commutative monoid has a monochromatic
-- homothetic copy. This file contains no proof.

module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Shrink
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Finite.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace Q764287

/-- Van der Waerden's theorem in its homothetic-copy form for additive commutative monoids. -/
theorem van_der_waerden_s_theorem {M κ : Type*} [AddCommMonoid M] (S : Finset M) [Finite κ]
    (C : M → κ) : ∃ a > 0, ∃ (b : M) (c : κ), ∀ s ∈ S, C (a • s + b) = c := sorry

end Q764287
