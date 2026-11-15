-- Statement-only formalization of Thousand Theorems artifact Q776578
-- (thousand-theorems__lean4__Q776578), "Artin–Wedderburn theorem": a semisimple
-- algebra is algebra-equivalent to a finite product of matrix algebras over
-- division algebras. This file contains no proof.

module

public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.SimpleRing.Matrix

@[expose] public section

namespace Q776578

universe u

/-- The algebra form of the Artin–Wedderburn theorem for a semisimple ring. -/
theorem exists_algEquiv_pi_matrix_divisionRing_statement
    (R₀ : Type*) (R : Type u) [CommSemiring R₀] [Ring R] [Algebra R₀ R]
    [IsSemisimpleRing R] :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i))
      (_ : ∀ i, Algebra R₀ (D i)), (∀ i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := sorry

end Q776578
