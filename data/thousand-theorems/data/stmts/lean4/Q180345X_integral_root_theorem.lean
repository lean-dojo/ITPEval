-- Statement-only formalization of Thousand Theorems artifact Q180345X
-- (thousand-theorems__lean4__Q180345X), "Integral root theorem": every root in
-- the fraction field of a unique factorization domain of a monic polynomial
-- over that domain is an integer over the domain. This file contains no proof.

module

public import Mathlib.Algebra.Polynomial.Eval.Algebra
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

@[expose] public section

open scoped Polynomial

namespace Q180345X

variable {A K : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Field K]
variable [Algebra A K] [IsFractionRing A K]

open IsLocalization Polynomial

/-- A root of a monic polynomial over a UFD is an integer over that domain. -/
theorem isInteger_of_is_root_of_monic {p : A[X]} (hp : Monic p) {r : K}
    (hr : aeval r p = 0) : IsInteger A r := sorry

end Q180345X
