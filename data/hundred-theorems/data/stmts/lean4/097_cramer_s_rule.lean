/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Regular.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Cramer's rule and adjugate matrices

The adjugate matrix is the transpose of the cofactor matrix.
It is calculated with Cramer's rule, which we introduce first.
The vectors returned by Cramer's rule are given by the linear map `cramer`,
which sends a matrix `A` and vector `b` to the vector consisting of the
determinant of replacing the `i`th column of `A` with `b` at index `i`
(written as `(A.updateCol i b).det`).
Using Cramer's rule, we can compute for each matrix `A` the matrix `adjugate A`.
The entries of the adjugate are the minors of `A`.
Instead of defining a minor by deleting row `i` and column `j` of `A`, we
replace the `i`th row of `A` with the `j`th basis vector; the resulting matrix
has the same determinant but more importantly equals Cramer's rule applied
to `A` and the `j`th basis vector, simplifying the subsequent proofs.
We prove the adjugate behaves like `det A • A⁻¹`.

## Main definitions

* `Matrix.cramer A b`: the vector output by Cramer's rule on `A` and `b`.
* `Matrix.adjugate A`: the adjugate (or classical adjoint) of the matrix `A`.

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

cramer, cramer's rule, adjugate
-/

@[expose] public section


namespace Matrix

universe u v w

variable {m : Type u} {n : Type v} {α : Type w}
variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

open Matrix Polynomial Equiv Equiv.Perm Finset

section Cramer

/-!
  ### `cramer` section

  Introduce the linear map `cramer` with values defined by `cramerMap`.
  After defining `cramerMap` and showing it is linear,
  we will restrict our proofs to using `cramer`.
-/


variable (A : Matrix n n α) (b : n → α)

/-- `cramerMap A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramerMap A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A * x = b` has a unique solution in `x`, `cramerMap A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramerMap` is well-defined but not necessarily useful.
-/
def cramerMap (i : n) : α :=
  (A.updateCol i b).det

theorem cramerMap_is_linear (i : n) : IsLinearMap α fun b => cramerMap A b i :=
  { map_add := det_updateCol_add _ _
    map_smul := det_updateCol_smul _ _ }

theorem cramer_is_linear : IsLinearMap α (cramerMap A) := by sorry
def cramer (A : Matrix n n α) : (n → α) →ₗ[α] (n → α) :=
  IsLinearMap.mk' (cramerMap A) (cramer_is_linear A)

theorem cramer_apply (i : n) : cramer A b i = (A.updateCol i b).det :=
  rfl

theorem cramer_transpose_apply (i : n) : cramer Aᵀ b i = (A.updateRow i b).det := by sorry
theorem cramer_transpose_row_self (i : n) : Aᵀ.cramer (A i) = Pi.single i A.det := by sorry
theorem cramer_row_self (i : n) (h : ∀ j, b j = A j i) : A.cramer b = Pi.single i A.det := by sorry
theorem cramer_one : cramer (1 : Matrix n n α) = 1 := by sorry
theorem cramer_smul (r : α) (A : Matrix n n α) :
    cramer (r • A) = r ^ (Fintype.card n - 1) • cramer A :=
  LinearMap.ext fun _ => funext fun _ => det_updateCol_smul_left _ _ _ _

@[simp]
theorem cramer_subsingleton_apply [Subsingleton n] (A : Matrix n n α) (b : n → α) (i : n) :
    cramer A b i = b i := by rw [cramer_apply, det_eq_elem_of_subsingleton _ i, updateCol_self]

theorem cramer_zero [Nontrivial n] : cramer (0 : Matrix n n α) = 0 := by sorry
theorem sum_cramer {β} (s : Finset β) (f : β → n → α) :
    (∑ x ∈ s, cramer A (f x)) = cramer A (∑ x ∈ s, f x) :=
  (map_sum (cramer A) ..).symm

/-- Use linearity of `cramer` and vector evaluation to take `cramer A _ i` out of a summation. -/
theorem sum_cramer_apply {β} (s : Finset β) (f : n → β → α) (i : n) :
    (∑ x ∈ s, cramer A (fun j => f j x) i) = cramer A (fun j : n => ∑ x ∈ s, f j x) i :=
  calc
    (∑ x ∈ s, cramer A (fun j => f j x) i) = (∑ x ∈ s, cramer A fun j => f j x) i :=
      (Finset.sum_apply i s _).symm
    _ = cramer A (fun j : n => ∑ x ∈ s, f j x) i := by sorry
theorem cramer_submatrix_equiv (A : Matrix m m α) (e : n ≃ m) (b : n → α) :
    cramer (A.submatrix e e) b = cramer A (b ∘ e.symm) ∘ e := by sorry
theorem cramer_reindex (e : m ≃ n) (A : Matrix m m α) (b : n → α) :
    cramer (reindex e e A) b = cramer A (b ∘ e) ∘ e.symm :=
  cramer_submatrix_equiv _ _ _

end Cramer

section Adjugate

/-!
### `adjugate` section

Define the `adjugate` matrix and a few equations.
These will hold for any matrix over a commutative ring.
-/


/-- The adjugate matrix is the transpose of the cofactor matrix.

  Typically, the cofactor matrix is defined by taking minors,
  i.e. the determinant of the matrix with a row and column removed.
  However, the proof of `mul_adjugate` becomes a lot easier if we use the
  matrix replacing a column with a basis vector, since it allows us to use
  facts about the `cramer` map.
-/
def adjugate (A : Matrix n n α) : Matrix n n α :=
  of fun i => cramer Aᵀ (Pi.single i 1)

theorem adjugate_def (A : Matrix n n α) : adjugate A = of fun i => cramer Aᵀ (Pi.single i 1) :=
  rfl

theorem adjugate_apply (A : Matrix n n α) (i j : n) :
    adjugate A i j = (A.updateRow j (Pi.single i 1)).det := by sorry
theorem adjugate_transpose (A : Matrix n n α) : (adjugate A)ᵀ = adjugate Aᵀ := by sorry
theorem IsSymm.adjugate {A : Matrix n n α} (hA : A.IsSymm) : A.adjugate.IsSymm := by sorry
theorem adjugate_submatrix_equiv_self (e : n ≃ m) (A : Matrix m m α) :
    adjugate (A.submatrix e e) = (adjugate A).submatrix e e := by sorry
theorem adjugate_reindex (e : m ≃ n) (A : Matrix m m α) :
    adjugate (reindex e e A) = reindex e e (adjugate A) :=
  adjugate_submatrix_equiv_self _ _

/-- Since the map `b ↦ cramer A b` is linear in `b`, it must be multiplication by some matrix. This
matrix is `A.adjugate`. -/
theorem cramer_eq_adjugate_mulVec (A : Matrix n n α) (b : n → α) :
    cramer A b = A.adjugate *ᵥ b := by sorry
theorem mul_adjugate_apply (A : Matrix n n α) (i j k) :
    A i k * adjugate A k j = cramer Aᵀ (Pi.single k (A i k)) j := by sorry
theorem mul_adjugate (A : Matrix n n α) : A * adjugate A = A.det • (1 : Matrix n n α) := by sorry
theorem adjugate_mul (A : Matrix n n α) : adjugate A * A = A.det • (1 : Matrix n n α) :=
  calc
    adjugate A * A = (Aᵀ * adjugate Aᵀ)ᵀ := by sorry
theorem adjugate_smul (r : α) (A : Matrix n n α) :
    adjugate (r • A) = r ^ (Fintype.card n - 1) • adjugate A := by sorry
theorem mulVec_cramer (A : Matrix n n α) (b : n → α) : A *ᵥ cramer A b = A.det • b := by sorry
theorem adjugate_subsingleton [Subsingleton n] (A : Matrix n n α) : adjugate A = 1 := by sorry
theorem adjugate_eq_one_of_card_eq_one {A : Matrix n n α} (h : Fintype.card n = 1) :
    adjugate A = 1 :=
  haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  adjugate_subsingleton _

@[simp]
theorem adjugate_zero [Nontrivial n] : adjugate (0 : Matrix n n α) = 0 := by sorry
theorem adjugate_one : adjugate (1 : Matrix n n α) = 1 := by sorry
theorem adjugate_diagonal (v : n → α) :
    adjugate (diagonal v) = diagonal fun i => ∏ j ∈ Finset.univ.erase i, v j := by sorry
theorem _root_.RingHom.map_adjugate {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix n n R) : f.mapMatrix M.adjugate = Matrix.adjugate (f.mapMatrix M) := by sorry
theorem _root_.AlgHom.map_adjugate {R A B : Type*} [CommSemiring R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (M : Matrix n n A) :
    f.mapMatrix M.adjugate = Matrix.adjugate (f.mapMatrix M) :=
  f.toRingHom.map_adjugate _

theorem det_adjugate (A : Matrix n n α) : (adjugate A).det = A.det ^ (Fintype.card n - 1) := by sorry
theorem adjugate_fin_zero (A : Matrix (Fin 0) (Fin 0) α) : adjugate A = 0 :=
  Subsingleton.elim _ _

@[simp]
theorem adjugate_fin_one (A : Matrix (Fin 1) (Fin 1) α) : adjugate A = 1 :=
  adjugate_subsingleton A

theorem adjugate_fin_succ_eq_det_submatrix {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) α) (i j) :
    adjugate A i j = (-1) ^ (j + i : ℕ) * det (A.submatrix j.succAbove i.succAbove) := by sorry
theorem adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) α) :
    adjugate A = !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by sorry
theorem adjugate_fin_two_of (a b c d : α) : adjugate !![a, b; c, d] = !![d, -b; -c, a] :=
  adjugate_fin_two _

theorem adjugate_fin_three (A : Matrix (Fin 3) (Fin 3) α) :
    adjugate A =
    !![A 1 1 * A 2 2 - A 1 2 * A 2 1,
      -(A 0 1 * A 2 2) + A 0 2 * A 2 1,
      A 0 1 * A 1 2 - A 0 2 * A 1 1;
      -(A 1 0 * A 2 2) + A 1 2 * A 2 0,
      A 0 0 * A 2 2 - A 0 2 * A 2 0,
      -(A 0 0 * A 1 2) + A 0 2 * A 1 0;
      A 1 0 * A 2 1 - A 1 1 * A 2 0,
      -(A 0 0 * A 2 1) + A 0 1 * A 2 0,
      A 0 0 * A 1 1 - A 0 1 * A 1 0] := by sorry
theorem adjugate_fin_three_of (a b c d e f g h i : α) :
    adjugate !![a, b, c; d, e, f; g, h, i] =
      !![  e * i  - f * h, -(b * i) + c * h,   b * f  - c * e;
         -(d * i) + f * g,   a * i  - c * g, -(a * f) + c * d;
           d * h  - e * g, -(a * h) + b * g,   a * e  - b * d] :=
  adjugate_fin_three _

theorem det_eq_sum_mul_adjugate_row (A : Matrix n n α) (i : n) :
    det A = ∑ j : n, A i j * adjugate A j i := by sorry
theorem det_eq_sum_mul_adjugate_col (A : Matrix n n α) (j : n) :
    det A = ∑ i : n, A i j * adjugate A j i := by sorry
theorem adjugate_conjTranspose [StarRing α] (A : Matrix n n α) : A.adjugateᴴ = adjugate Aᴴ := by sorry
theorem isRegular_of_isLeftRegular_det {A : Matrix n n α} (hA : IsLeftRegular A.det) :
    IsRegular A := by sorry
theorem adjugate_mul_distrib_aux (A B : Matrix n n α) (hA : IsLeftRegular A.det)
    (hB : IsLeftRegular B.det) : adjugate (A * B) = adjugate B * adjugate A := by sorry
theorem adjugate_mul_distrib (A B : Matrix n n α) : adjugate (A * B) = adjugate B * adjugate A := by sorry
theorem adjugate_pow (A : Matrix n n α) (k : ℕ) : adjugate (A ^ k) = adjugate A ^ k := by sorry
theorem det_smul_adjugate_adjugate (A : Matrix n n α) :
    det A • adjugate (adjugate A) = det A ^ (Fintype.card n - 1) • A := by sorry
theorem adjugate_adjugate (A : Matrix n n α) (h : Fintype.card n ≠ 1) :
    adjugate (adjugate A) = det A ^ (Fintype.card n - 2) • A := by sorry
theorem adjugate_adjugate' (A : Matrix n n α) [Nontrivial n] :
    adjugate (adjugate A) = det A ^ (Fintype.card n - 2) • A :=
  adjugate_adjugate _ <| Fintype.one_lt_card.ne'

end Adjugate

end Matrix
