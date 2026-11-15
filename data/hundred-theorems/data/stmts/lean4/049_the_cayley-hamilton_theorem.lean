/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.MatrixPolynomialAlgebra

/-!
# Characteristic polynomials and the Cayley-Hamilton theorem

We define characteristic polynomials of matrices and
prove the Cayley–Hamilton theorem over arbitrary commutative rings.

See the file `Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean` for corollaries of this theorem.

## Main definitions

* `Matrix.charpoly` is the characteristic polynomial of a matrix.

## Implementation details

We follow a nice proof from http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
-/

@[expose] public section

noncomputable section

universe u v w

namespace Matrix

open Finset Matrix Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]
variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)
variable (i j : n)


/-- The "characteristic matrix" of `M : Matrix n n R` is the matrix of polynomials $t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
def charmatrix (M : Matrix n n R) : Matrix n n R[X] :=
  Matrix.scalar n (X : R[X]) - (C : R →+* R[X]).mapMatrix M

theorem charmatrix_apply :
    charmatrix M i j = (Matrix.diagonal fun _ : n => X) i j - C (M i j) :=
  rfl

@[simp]
theorem charmatrix_apply_eq : charmatrix M i i = (X : R[X]) - C (M i i) := by sorry
theorem charmatrix_apply_ne (h : i ≠ j) : charmatrix M i j = -C (M i j) := by sorry
theorem charmatrix_zero : charmatrix (0 : Matrix n n R) = Matrix.scalar n (X : R[X]) := by sorry
theorem charmatrix_diagonal (d : n → R) :
    charmatrix (diagonal d) = diagonal fun i => X - C (d i) := by sorry
theorem charmatrix_one : charmatrix (1 : Matrix n n R) = diagonal fun _ => X - 1 :=
  charmatrix_diagonal _

@[simp]
theorem charmatrix_natCast (k : ℕ) :
    charmatrix (k : Matrix n n R) = diagonal fun _ => X - (k : R[X]) :=
  charmatrix_diagonal _

@[simp]
theorem charmatrix_ofNat (k : ℕ) [k.AtLeastTwo] :
    charmatrix (ofNat(k) : Matrix n n R) = diagonal fun _ => X - ofNat(k) :=
  charmatrix_natCast _

@[simp]
theorem charmatrix_transpose (M : Matrix n n R) : (Mᵀ).charmatrix = M.charmatrixᵀ := by sorry
theorem matPolyEquiv_charmatrix : matPolyEquiv (charmatrix M) = X - C M := by sorry
theorem charmatrix_reindex (e : n ≃ m) :
    charmatrix (reindex e e M) = reindex e e (charmatrix M) := by sorry
lemma charmatrix_map (M : Matrix n n R) (f : R →+* S) :
    charmatrix (M.map f) = (charmatrix M).map (Polynomial.map f) := by sorry
lemma charmatrix_fromBlocks :
    charmatrix (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (charmatrix M₁₁) (- M₁₂.map C) (- M₂₁.map C) (charmatrix M₂₂) := by sorry
lemma charmatrix_blockTriangular_iff {α : Type*} [Preorder α] {M : Matrix n n R} {b : n → α} :
    M.charmatrix.BlockTriangular b ↔ M.BlockTriangular b := by sorry
def charpoly (M : Matrix n n R) : R[X] :=
  (charmatrix M).det

theorem eval_charpoly (M : Matrix m m R) (t : R) :
    M.charpoly.eval t = (Matrix.scalar _ t - M).det := by sorry
theorem charpoly_isEmpty [IsEmpty n] {A : Matrix n n R} : charpoly A = 1 := by sorry
theorem charpoly_zero : charpoly (0 : Matrix n n R) = X ^ Fintype.card n := by sorry
theorem charpoly_diagonal (d : n → R) : charpoly (diagonal d) = ∏ i, (X - C (d i)) := by sorry
theorem charpoly_one : charpoly (1 : Matrix n n R) = (X - 1) ^ Fintype.card n := by sorry
theorem charpoly_natCast (k : ℕ) :
    charpoly (k : Matrix n n R) = (X - (k : R[X])) ^ Fintype.card n := by sorry
theorem charpoly_ofNat (k : ℕ) [k.AtLeastTwo] :
    charpoly (ofNat(k) : Matrix n n R) = (X - ofNat(k)) ^ Fintype.card n :=
  charpoly_natCast _

@[simp]
theorem charpoly_transpose (M : Matrix n n R) : (Mᵀ).charpoly = M.charpoly := by sorry
theorem charpoly_reindex (e : n ≃ m)
    (M : Matrix n n R) : (reindex e e M).charpoly = M.charpoly := by sorry
lemma charpoly_map (M : Matrix n n R) (f : R →+* S) :
    (M.map f).charpoly = M.charpoly.map f := by sorry
lemma charpoly_fromBlocks_zero₁₂ :
    (fromBlocks M₁₁ 0 M₂₁ M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by sorry
lemma charpoly_fromBlocks_zero₂₁ :
    (fromBlocks M₁₁ M₁₂ 0 M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by sorry
lemma charmatrix_toSquareBlock {α : Type*} [DecidableEq α] {b : n → α} {a : α} :
    (M.toSquareBlock b a).charmatrix = M.charmatrix.toSquareBlock b a := by sorry
lemma BlockTriangular.charpoly {α : Type*} {b : n → α} [LinearOrder α] (h : M.BlockTriangular b) :
    M.charpoly = ∏ a ∈ image b univ, (M.toSquareBlock b a).charpoly := by sorry
lemma charpoly_of_upperTriangular [LinearOrder n] (M : Matrix n n R) (h : M.BlockTriangular id) :
    M.charpoly = ∏ i : n, (X - C (M i i)) := by sorry
theorem aeval_self_charpoly (M : Matrix n n R) : aeval M M.charpoly = 0 := by sorry
theorem charpoly_mul_comm' (A : Matrix m n R) (B : Matrix n m R) :
    X ^ Fintype.card n * (A * B).charpoly = X ^ Fintype.card m * (B * A).charpoly := by sorry
theorem charpoly_mul_comm_of_le
    (A : Matrix m n R) (B : Matrix n m R) (hle : Fintype.card n ≤ Fintype.card m) :
    (A * B).charpoly = X ^ (Fintype.card m - Fintype.card n) * (B * A).charpoly := by sorry
theorem charpoly_mul_comm (A B : Matrix n n R) : (A * B).charpoly = (B * A).charpoly :=
  (isRegular_X_pow _).left.eq_iff.mp <| charpoly_mul_comm' A B

theorem charpoly_vecMulVec (u v : n → R) :
    (vecMulVec u v).charpoly = X ^ Fintype.card n - (u ⬝ᵥ v) • X ^ (Fintype.card n - 1) := by sorry
theorem charpoly_units_conj (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M.val * N * M⁻¹.val).charpoly = N.charpoly := by sorry
theorem charpoly_units_conj' (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M⁻¹.val * N * M.val).charpoly = N.charpoly :=
  charpoly_units_conj M⁻¹ N

set_option backward.isDefEq.respectTransparency false in
theorem charpoly_sub_scalar (M : Matrix n n R) (μ : R) :
    (M - scalar n μ).charpoly = M.charpoly.comp (X + C μ) := by sorry
end Matrix
