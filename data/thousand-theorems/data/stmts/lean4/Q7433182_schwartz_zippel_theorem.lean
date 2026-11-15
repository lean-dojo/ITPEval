-- Statement-only formalization of Thousand Theorems artifact Q7433182
-- (thousand-theorems__lean4__Q7433182), "Schwartz–Zippel theorem": a nonzero
-- multivariable polynomial over an integral domain has its normalized count
-- of zeros on a dependent product of finite sets bounded by a support-degree supremum.
-- This file contains no proof.

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.Order.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.Finset
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fin.Tuple.Finset

@[expose] public section

open Fin Finset Fintype

namespace Q7433182

local notation:70 s:70 " ^^ " n:71 => piFinset fun i : Fin n ↦ s i

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

/-- The sharp dependent-product form of the Schwartz–Zippel theorem. -/
theorem schwartz_zippel_sup_sum_statement :
    ∀ {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0) (S : Fin n → Finset R),
      #{x ∈ S ^^ n | MvPolynomial.eval x p = 0} / ∏ i, (#(S i) : ℚ≥0) ≤
        p.support.sup fun s ↦ ∑ i, (s i / #(S i) : ℚ≥0) := sorry

end Q7433182
