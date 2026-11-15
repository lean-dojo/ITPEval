-- Statement-only formalization of Thousand Theorems artifact Q1816952
-- (thousand-theorems__lean4__Q1816952), "Schur's lemma": over an algebraically
-- closed field, the finite-dimensional endomorphism space of a simple object in
-- a linear category with kernels has dimension one. This file contains no proof.

import Mathlib.CategoryTheory.Preadditive.Schur

namespace Q1816952

open CategoryTheory CategoryTheory.Limits Module

/-- Schur's lemma for endomorphisms of a simple object in a linear category. -/
theorem finrank_endomorphism_simple_eq_one_statement
    {C : Type*} [Category* C] [Preadditive C]
    (𝕜 : Type*) [Field 𝕜] [IsAlgClosed 𝕜] [Linear 𝕜 C] [HasKernels C]
    (X : C) [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)] :
    finrank 𝕜 (X ⟶ X) = 1 := sorry

end Q1816952
