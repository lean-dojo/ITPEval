-- Statement-only formalization of Thousand Theorems artifact Q1068976
-- (thousand-theorems__lean4__Q1068976), "Hilbert's Nullstellensatz": for
-- polynomials over a field, evaluated in an algebraically closed extension,
-- the ideal vanishing on an ideal's zero locus is its radical. This file
-- contains no proof.

module

public import Mathlib.RingTheory.Nullstellensatz

@[expose] public section

noncomputable section

namespace Q1068976

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {σ : Type*} [IsAlgClosed K] [Finite σ]

/-- Hilbert's Nullstellensatz for multivariate polynomial ideals over a field. -/
theorem hilbert_nullstellensatz_statement (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus K I) = I.radical := sorry

end Q1068976
