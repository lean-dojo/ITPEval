-- Statement-only formalization of Thousand Theorems artifact Q3527205
-- (thousand-theorems__lean4__Q3527205), "Dimension theorem for vector spaces":
-- over a semiring satisfying invariant basis number, any two bases of the same
-- module have index types of equal cardinality. This file contains no proof.

module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.InvariantBasisNumber

@[expose] public section

universe u v w w'

open Cardinal Module

namespace Q3527205

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
variable {ι : Type w} {ι' : Type w'}

/-- Any two bases of a module over a semiring with invariant basis number have
index types of equal cardinality. -/
theorem mk_eq_mk_of_basis_statement [InvariantBasisNumber R]
    (v : Basis ι R M) (v' : Basis ι' R M) :
    Cardinal.lift.{w'} #ι = Cardinal.lift.{w} #ι' := sorry

end Q3527205
