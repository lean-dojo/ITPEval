-- Statement-only formalization of Thousand Theorems artifact Q180345
-- (thousand-theorems__lean4__Q180345), "Rational root theorem": for a polynomial
-- over a unique factorization domain, the numerator of a root in its fraction field
-- divides the constant coefficient, and its denominator divides the leading coefficient.
-- This file contains no proof.

module

public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

open scoped Polynomial

section RationalRootTheorem

variable {A K : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Field K]
variable [Algebra A K] [IsFractionRing A K]

open IsFractionRing Polynomial

/-- The numerator of a root divides the polynomial's constant coefficient. -/
theorem num_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) :
    num A r ∣ p.coeff 0 := sorry

/-- The denominator of a root divides the polynomial's leading coefficient. -/
theorem den_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) :
    (den A r : A) ∣ p.leadingCoeff := sorry

end RationalRootTheorem
