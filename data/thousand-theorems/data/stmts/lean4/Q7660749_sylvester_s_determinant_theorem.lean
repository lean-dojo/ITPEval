-- Statement-only formalization of Thousand Theorems artifact Q7660749
-- (thousand-theorems__lean4__Q7660749), "Sylvester's determinant theorem":
-- over a commutative ring, det(I + AB) = det(I + BA) for rectangular matrices
-- of compatible finite dimensions. This file contains no proof.

module

import Mathlib.Data.Matrix.Mul
import Mathlib.GroupTheory.Perm.Sign

namespace Q7660749

open Finset

noncomputable section

variable {m n α : Type*}
variable [Fintype m] [Fintype n]
variable [DecidableEq m] [DecidableEq n]
variable [CommRing α]

/-- The determinant in its Leibniz permutation-sum form. -/
def matrixDet {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι α) : α :=
  ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤˣ) : α) * ∏ i, M (σ i) i

/-- Sylvester's determinant theorem for rectangular matrices over a commutative ring. -/
theorem sylvester_s_determinant_theorem (A : Matrix m n α) (B : Matrix n m α) :
    matrixDet (1 + A * B) = matrixDet (1 + B * A) := sorry

end
end Q7660749
