(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun bigop finset nmodule fingroup perm.
From mathcomp Require Import order algebra divalg countalg finalg zmodp.

(******************************************************************************)
(* Basic concrete linear algebra : definition of type for matrices, and all   *)
(* basic matrix operations including determinant, trace and support for block *)
(* decomposition. Matrices are represented by a row-major list of their       *)
(* coefficients but this implementation is hidden by three levels of wrappers *)
(* (Matrix/Finfun/Tuple) so the matrix type should be treated as abstract and *)
(* handled using only the operations described below:                         *)
(*   'M[R]_(m, n) == the type of m rows by n columns matrices with            *)
(*   'M_(m, n)       coefficients in R; the [R] is optional and is usually    *)
(*                   omitted.                                                 *)
(*  'M[R]_n, 'M_n == the type of n x n square matrices.                       *)
(* 'rV[R]_n, 'rV_n == the type of 1 x n row vectors.                          *)
(* 'cV[R]_n, 'cV_n == the type of n x 1 column vectors.                       *)
(*  \matrix_(i < m, j < n) Expr(i, j) ==                                      *)
(*                   the m x n matrix with general coefficient Expr(i, j),    *)
(*                   with i : 'I_m and j : 'I_n. the < m bound can be omitted *)
(*                   if it is equal to n, though usually both bounds are      *)
(*                   omitted as they can be inferred from the context.        *)
(*  \row_(j < n) Expr(j), \col_(i < m) Expr(i)                                *)
(*                   the row / column vectors with general term Expr; the     *)
(*                   parentheses can be omitted along with the bound.         *)
(* \matrix_(i < m) RowExpr(i) ==                                              *)
(*                   the m x n matrix with row i given by RowExpr(i) : 'rV_n. *)
(*          A i j == the coefficient of matrix A : 'M_(m, n) in column j of   *)
(*                   row i, where i : 'I_m, and j : 'I_n (via the coercion    *)
(*                   fun_of_matrix : matrix >-> Funclass).                    *)
(*     const_mx a == the constant matrix whose entries are all a (dimensions  *)
(*                   should be determined by context).                        *)
(*     map_mx f A == the pointwise image of A by f, i.e., the matrix Af       *)
(*                   congruent to A with Af i j = f (A i j) for all i and j.  *)
(*     map2_mx f A B == the pointwise image of A and B by f, i.e., the matrix *)
(*                     ABf congruent to A with ABf i j = f (A i j) (B i j)    *)
(*                     for all i and j.                                       *)
(*            A^T == the matrix transpose of A.                               *)
(*        row i A == the i'th row of A (this is a row vector).                *)
(*        col j A == the j'th column of A (a column vector).                  *)
(*       row' i A == A with the i'th row spliced out.                         *)
(*       col' i A == A with the j'th column spliced out.                      *)
(*   xrow i1 i2 A == A with rows i1 and i2 interchanged.                      *)
(*   xcol j1 j2 A == A with columns j1 and j2 interchanged.                   *)
(*   row_perm s A == A : 'M_(m, n) with rows permuted by s : 'S_m.            *)
(*   col_perm s A == A : 'M_(m, n) with columns permuted by s : 'S_n.         *)
(*   row_mx Al Ar == the row block matrix <Al Ar> obtained by concatenating   *)
(*                   two matrices Al and Ar of the same height.               *)
(*   col_mx Au Ad == the column block matrix / Au \ (Au and Ad must have the  *)
(*                   same width).            \ Ad /                           *)
(* block_mx Aul Aur Adl Adr == the block matrix / Aul Aur \                   *)
(*                                              \ Adl Adr /                   *)
(* \mxblock_(i < m, j < n) B i j                                              *)
(*                == the block matrix of type 'M_(\sum_i p_ i, \sum_j q_ j)   *)
(*                             / (B 0 0) ⋯ (B 0 j) ⋯ (B 0 n) \                *)
(*                             |   ...       ...       ...   |                *)
(*                             | (B i 0) ⋯ (B i j) ⋯ (B i n) |                *)
(*                             |   ...       ...       ...   |                *)
(*                             \ (B m 0) ⋯ (B m j) ⋯ (B m n) /                *)
(*                   where each block (B i j) has type 'M_(p_ i, q_ j).       *)
(* \mxdiag_(i < n) B i == the block square matrix of type 'M_(\sum_i p_ i)    *)
(*                                / (B 0)      0      \                       *)
(*                                |     ...     ...   |                       *)
(*                                |  0    (B i)    0  |                       *)
(*                                |   ...     ...     |                       *)
(*                                \      0      (B n) /                       *)
(*                        where each block (B i) has type 'M_(p_ i).          *)
(*  \mxrow_(j < n) B j ==  the block matrix of type 'M_(m, \sum_j q_ j).      *)
(*                                 < (B 0) ... (B n) >                        *)
(*                         where each block (B j) has type 'M_(m, q_ j).      *)
(*  \mxcol_(i < m) B i ==  the block matrix of type 'M_(\sum_i p_ i, n)       *)
(*                                      / (B 0) \                             *)
(*                                      |  ...  |                             *)
(*                                      \ (B m) /                             *)
(*                         where each block (B i) has type 'M(p_ i, n).       *)
(*   [l|r]submx A == the left/right submatrices of a row block matrix A.      *)
(*                   Note that the type of A, 'M_(m, n1 + n2) indicates how A *)
(*                   should be decomposed.                                    *)
(*   [u|d]submx A == the up/down submatrices of a column block matrix A.      *)
(* [u|d][l|r]submx A == the upper left, etc submatrices of a block matrix A.  *)
(*  submxblock A i j == the block submatrix of type 'M_(p_ i, q_ j) of A.     *)
(*                      The type of A, 'M_(\sum_i p_ i, \sum_i q_ i)          *)
(*                      indicates how A should be decomposed.                 *)
(*                      There is no analogous for mxdiag since one can use    *)
(*                      submxblock A i i to extract a diagonal block.         *)
(*   submxrow A j == the submatrix of type 'M_(m, q_ j) of A. The type of A,  *)
(*                   'M_(m, \sum_j q_ j) indicates how A should be decomposed.*)
(*   submxrow A j == the submatrix of type 'M_(p_ i, n) of A. The type of A,  *)
(*                   'M_(\sum_i p_ i, n) indicates how A should be decomposed.*)
(*    mxsub f g A == generic reordered submatrix, given by functions f and g  *)
(*                   which specify which subset of rows and columns to take   *)
(*                   and how to reorder them, e.g. picking f and g to be      *)
(*                   increasing yields traditional submatrices.               *)
(*                := \matrix_(i, j) A (f i) (g i)                             *)
(*     rowsub f A := mxsub f id A                                             *)
(*     colsub g A := mxsub id g A                                             *)
(* castmx eq_mn A == A : 'M_(m, n) cast to 'M_(m', n') using the equation     *)
(*                   pair eq_mn : (m = m') * (n = n'). This is the usual      *)
(*                   workaround for the syntactic limitations of dependent    *)
(*                   types in Coq, and can be used to introduce a block       *)
(*                   decomposition. It simplifies to A when eq_mn is the      *)
(*                   pair (erefl m, erefl n) (using rewrite /castmx /=).      *)
(* conform_mx B A == A if A and B have the same dimensions, else B.           *)
(*        mxvec A == a row vector of width m * n holding all the entries of   *)
(*                   the m x n matrix A.                                      *)
(* mxvec_index i j == the index of A i j in mxvec A.                          *)
(*       vec_mx v == the inverse of mxvec, reshaping a vector of width m * n  *)
(*                   back into into an m x n rectangular matrix.              *)
(* In 'M[R]_(m, n), R can be any type, but 'M[R]_(m, n) inherits the eqType,  *)
(* choiceType, countType, finType, nmodType, and zmodType structures from R;  *)
(* 'M[R]_(m, n) also forms a natural lmodType R when R is a pzRingType.       *)
(* Square matrices of type 'M[R]_n (resp. non-trivial square matrices of type *)
(* 'M[R]_n.+1) inherit the pz(Semi)RingType (resp. nz(Semi)RingType) structure*)
(* from R; indeed they then have an algebra structure (lalgType R, or algType *)
(* R if R is a comNzRingType, or even unitAlgType if R is a comUnitRingType). *)
(*   We thus provide separate syntax for the general matrix multiplication,   *)
(* and other operations for matrices over a pzRingType R:                     *)
(*         A *m B == the matrix product of A and B; the width of A must be    *)
(*                   equal to the height of B.                                *)
(*           a%:M == the scalar matrix with a's on the main diagonal; in      *)
(*                   particular 1%:M denotes the identity matrix, and is      *)
(*                   equal to 1%R when n is of the form n'.+1 (e.g., n >= 1). *)
(* is_scalar_mx A <=> A is a scalar matrix (A = a%:M for some A).             *)
(*      diag_mx d == the diagonal matrix whose main diagonal is d : 'rV_n.    *)
(*  is_diag_mx A <=> A is a diagonal matrix:  forall i j, i != j -> A i j = 0 *)
(*  is_trig_mx A <=> A is a triangular matrix: forall i j, i < j -> A i j = 0 *)
(*   delta_mx i j == the matrix with a 1 in row i, column j and 0 elsewhere.  *)
(*       pid_mx r == the partial identity matrix with 1s only on the r first  *)
(*                   coefficients of the main diagonal; the dimensions of     *)
(*                   pid_mx r are determined by the context, and pid_mx r can *)
(*                   be rectangular.                                          *)
(*     copid_mx r == the complement to 1%:M of pid_mx r: a square diagonal    *)
(*                   matrix with 1s on all but the first r coefficients on    *)
(*                   its main diagonal.                                       *)
(*      perm_mx s == the n x n permutation matrix for s : 'S_n.               *)
(* tperm_mx i1 i2 == the permutation matrix that exchanges i1 i2 : 'I_n.      *)
(*   is_perm_mx A == A is a permutation matrix.                               *)
(*     lift0_mx A == the 1 + n square matrix block_mx 1 0 0 A when A : 'M_n.  *)
(*          \tr A == the trace of a square matrix A.                          *)
(*         \det A == the determinant of A, using the Leibnitz formula.        *)
(* cofactor i j A == the i, j cofactor of A (the signed i, j minor of A),     *)
(*         \adj A == the adjugate matrix of A (\adj A i j = cofactor j i A).  *)
(*   A \in unitmx == A is invertible (R must be a comUnitRingType).           *)
(*        invmx A == the inverse matrix of A if A \in unitmx A, otherwise A.  *)
(* A \is a mxOver S == the matrix A has its coefficients in S.                *)
(*       comm_mx A B := A *m B = B *m A                                       *)
(*      comm_mxb A B := A *m B == B *m A                                      *)
(* all_comm_mx As fs := all2rel comm_mxb fs                                   *)
(* The following operations provide a correspondence between linear functions *)
(* and matrices:                                                              *)
(*     lin1_mx f == the m x n matrix that emulates via right product          *)
(*                  a (linear) function f : 'rV_m -> 'rV_n on ROW VECTORS     *)
(*      lin_mx f == the (m1 * n1) x (m2 * n2) matrix that emulates, via the   *)
(*                  right multiplication on the mxvec encodings, a linear     *)
(*                  function f : 'M_(m1, n1) -> 'M_(m2, n2)                   *)
(* lin_mul_row u := lin1_mx (mulmx u \o vec_mx) (applies a row-encoded        *)
(*                  function to the row-vector u).                            *)
(*       mulmx A == partially applied matrix multiplication (mulmx A B is     *)
(*                  displayed as A *m B), with, for A : 'M_(m, n), a          *)
(*                  canonical {linear 'M_(n, p) -> 'M(m, p}} structure.       *)
(*      mulmxr A == self-simplifying right-hand matrix multiplication, i.e.,  *)
(*                  mulmxr A B simplifies to B *m A, with, for A : 'M_(n, p), *)
(*                  a canonical {linear 'M_(m, n) -> 'M(m, p}} structure.     *)
(*   lin_mulmx A := lin_mx (mulmx A).                                         *)
(*  lin_mulmxr A := lin_mx (mulmxr A).                                        *)
(* We also extend any finType structure of R to 'M[R]_(m, n), and define:     *)
(*     {'GL_n[R]} == the finGroupType of units of 'M[R]_n.-1.+1.              *)
(*      'GL_n[R]  == the general linear group of all matrices in {'GL_n(R)}.  *)
(*      'GL_n(p)  == 'GL_n['F_p], the general linear group of a prime field.  *)
(*       GLval u  == the coercion of u : {'GL_n(R)} to a matrix.              *)
(*   In addition to the lemmas relevant to these definitions, this file also  *)
(* proves several classic results, including :                                *)
(* - The determinant is a multilinear alternate form.                         *)
(* - The Laplace determinant expansion formulas: expand_det_[row|col].        *)
(* - The Cramer rule : mul_mx_adj & mul_adj_mx.                               *)
(* Vandermonde m a == the 'M[R]_(m, n) Vandermonde matrix, given a : 'rV_n    *)
(*                    /         1          ...           1              \     *)
(*                    |      (a 0 0)       ...      (a 0 (n - 1))       |     *)
(*                    |    (a 0 0 ^+ 2)    ...    (a 0 (n - 1) ^+ 2)    |     *)
(*                    |        ...                      ...             |     *)
(*                    \ (a 0 0 ^+ (m - 1)) ... (a 0 (n - 1) ^+ (m - 1)) /     *)
(*                 := \matrix_(i < m, j < n) a 0 j ^+ i.                      *)
(* Finally, as an example of the use of block products, we program and prove  *)
(* the correctness of a classical linear algebra algorithm:                   *)
(*   cormen_lup A == the triangular decomposition (L, U, P) of a nontrivial   *)
(*                   square matrix A into a lower triagular matrix L with 1s  *)
(*                   on the main diagonal, an upper matrix U, and a           *)
(*                   permutation matrix P, such that P * A = L * U.           *)
(* This is example only; we use a different, more precise algorithm to        *)
(* develop the theory of matrix ranks and row spaces in mxalgebra.v           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope group_scope.
Import GRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "''M_' n"     (at level 0, n at level 2, format "''M_' n").
Reserved Notation "''rV_' n"    (at level 0, n at level 2, format "''rV_' n").
Reserved Notation "''cV_' n"    (at level 0, n at level 2, format "''cV_' n").
Reserved Notation "''M_' ( n )". (* only parsing *)
Reserved Notation "''M_' ( m , n )" (format "''M_' ( m ,  n )").
Reserved Notation "''M[' R ]_ n"    (at level 0, n at level 2). (* only parsing *)
Reserved Notation "''rV[' R ]_ n"   (at level 0, n at level 2). (* only parsing *)
Reserved Notation "''cV[' R ]_ n"   (at level 0, n at level 2). (* only parsing *)
Reserved Notation "''M[' R ]_ ( n )". (* only parsing *)
Reserved Notation "''M[' R ]_ ( m , n )". (* only parsing *)

Reserved Notation "\matrix_ i E"
  (at level 34, E at level 39, i at level 2, format "\matrix_ i  E").
Reserved Notation "\matrix_ ( i < n ) E"
  (at level 34, E at level 39, i, n at level 50). (* only parsing *)
Reserved Notation "\matrix_ ( i , j ) E"
  (E at level 39, j at level 50, format "\matrix_ ( i ,  j )  E").
Reserved Notation "\matrix[ k ]_ ( i , j ) E"
  (at level 34, E at level 39, i, j at level 50,
   format "\matrix[ k ]_ ( i ,  j )  E").
Reserved Notation "\matrix_ ( i < m , j < n ) E"
  (E at level 39, j, n at level 50). (* only parsing *)
Reserved Notation "\matrix_ ( i , j < n ) E"
  (E at level 39, n at level 50). (* only parsing *)
Reserved Notation "\row_ j E"
  (at level 34, E at level 39, j at level 2, format "\row_ j  E").
Reserved Notation "\row_ ( j < n ) E"
  (at level 34, E at level 39, j, n at level 50). (* only parsing *)
Reserved Notation "\col_ j E"
  (at level 34, E at level 39, j at level 2, format "\col_ j  E").
Reserved Notation "\col_ ( j < n ) E"
  (at level 34, E at level 39, j, n at level 50). (* only parsing *)
Reserved Notation "\mxblock_ ( i , j ) E"
  (at level 34, E at level 39, i, j at level 50,
   format "\mxblock_ ( i ,  j )  E").
Reserved Notation "\mxblock_ ( i < m , j < n ) E"
  (E at level 39, m, j, n at level 50). (* only parsing *)
Reserved Notation "\mxblock_ ( i , j < n ) E"
  (E at level 39, n at level 50). (* only parsing *)
Reserved Notation "\mxrow_ j E"
  (at level 34, E at level 39, j at level 2, format "\mxrow_ j  E").
Reserved Notation "\mxrow_ ( j < n ) E"
  (at level 34, E at level 39, j, n at level 50). (* only parsing *)
Reserved Notation "\mxcol_ j E"
  (at level 34, E at level 39, j at level 2, format "\mxcol_ j  E").
Reserved Notation "\mxcol_ ( j < n ) E"
  (at level 34, E at level 39, j, n at level 50). (* only parsing *)
Reserved Notation "\mxdiag_ j E"
  (at level 34, E at level 39, j at level 2, format "\mxdiag_ j  E").
Reserved Notation "\mxdiag_ ( j < n ) E"
  (at level 34, E at level 39, j, n at level 50). (* only parsing *)

Reserved Notation "x %:M"   (format "x %:M").
Reserved Notation "A *m B" (at level 40, left associativity, format "A  *m  B").
Reserved Notation "A ^T"    (format "A ^T").
Reserved Notation "\tr A"   (at level 10, A at level 8, format "\tr  A").
Reserved Notation "\det A"  (at level 10, A at level 8, format "\det  A").
Reserved Notation "\adj A"  (at level 10, A at level 8, format "\adj  A").

Reserved Notation "{ ''GL_' n [ R ] }"
  (n at level 2, format "{ ''GL_' n [ R ] }").
Reserved Notation "{ ''GL_' n ( p ) }"
  (p at level 10, format "{ ''GL_' n ( p ) }").

Local Notation simp := (Monoid.Theory.simpm, oppr0).

(*****************************************************************************)
(****************************Type Definition**********************************)
(*****************************************************************************)

Section MatrixDef.

Variable R : Type.
Variables m n : nat.

(* Basic linear algebra (matrices).                                       *)
(* We use dependent types (ordinals) for the indices so that ranges are   *)
(* mostly inferred automatically                                          *)

Variant matrix : predArgType := Matrix of {ffun 'I_m * 'I_n -> R}.

Definition mx_val A := let: Matrix g := A in g.

HB.instance Definition _ := [isNew for mx_val].

Definition fun_of_matrix A (i : 'I_m) (j : 'I_n) := mx_val A (i, j).

Coercion fun_of_matrix : matrix >-> Funclass.

End MatrixDef.

Fact matrix_key : unit.
Proof.
Admitted.

HB.lock
Definition matrix_of_fun R (m n : nat) (k : unit) (F : 'I_m -> 'I_n -> R) :=
  @Matrix R m n [ffun ij => F ij.1 ij.2].
Canonical matrix_unlockable := Unlockable matrix_of_fun.unlock.

Section MatrixDef2.

Variable R : Type.
Variables m n : nat.
Implicit Type F : 'I_m -> 'I_n -> R.

Lemma mxE k F : matrix_of_fun k F =2 F.
Proof.
Admitted.

Lemma matrixP (A B : matrix R m n) : A =2 B <-> A = B.
Proof.
Admitted.

Lemma eq_mx k F1 F2 : (F1 =2 F2) -> matrix_of_fun k F1 = matrix_of_fun k F2.
Proof.
Admitted.

End MatrixDef2.

Arguments eq_mx {R m n k} [F1] F2 eq_F12.

Bind Scope ring_scope with matrix.

Notation "''M[' R ]_ ( m , n )" := (matrix R m n) (only parsing): type_scope.
Notation "''rV[' R ]_ n" := 'M[R]_(1, n) (only parsing) : type_scope.
Notation "''cV[' R ]_ n" := 'M[R]_(n, 1) (only parsing) : type_scope.
Notation "''M[' R ]_ n" := 'M[R]_(n, n) (only parsing) : type_scope.
Notation "''M[' R ]_ ( n )" := 'M[R]_n (only parsing) : type_scope.
Notation "''M_' ( m , n )" := 'M[_]_(m, n) : type_scope.
Notation "''rV_' n" := 'M_(1, n) : type_scope.
Notation "''cV_' n" := 'M_(n, 1) : type_scope.
Notation "''M_' n" := 'M_(n, n) : type_scope.
Notation "''M_' ( n )" := 'M_n (only parsing) : type_scope.

Notation "\matrix[ k ]_ ( i , j ) E" := (matrix_of_fun k (fun i j => E)) :
   ring_scope.

Notation "\matrix_ ( i < m , j < n ) E" :=
  (@matrix_of_fun _ m n matrix_key (fun i j => E)) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j < n ) E" :=
  (\matrix_(i < n, j < n) E) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j ) E" := (\matrix_(i < _, j < _) E) : ring_scope.

Notation "\matrix_ ( i < m ) E" :=
  (\matrix_(i < m, j < _) @fun_of_matrix _ 1 _ E 0 j)
  (only parsing) : ring_scope.
Notation "\matrix_ i E" := (\matrix_(i < _) E) : ring_scope.

Notation "\col_ ( i < n ) E" := (@matrix_of_fun _ n 1 matrix_key (fun i _ => E))
  (only parsing) : ring_scope.
Notation "\col_ i E" := (\col_(i < _) E) : ring_scope.

Notation "\row_ ( j < n ) E" := (@matrix_of_fun _ 1 n matrix_key (fun _ j => E))
  (only parsing) : ring_scope.
Notation "\row_ j E" := (\row_(j < _) E) : ring_scope.

HB.instance Definition _ (R : eqType) m n := [Equality of 'M[R]_(m, n) by <:].
HB.instance Definition _ (R : choiceType) m n := [Choice of 'M[R]_(m, n) by <:].
HB.instance Definition _ (R : countType) m n := [Countable of 'M[R]_(m, n) by <:].
HB.instance Definition _ (R : finType) m n := [Finite of 'M[R]_(m, n) by <:].

Lemma card_mx (F : finType) m n : (#|{: 'M[F]_(m, n)}| = #|F| ^ (m * n))%N.
Proof.
Admitted.

(*****************************************************************************)
(****** Matrix structural operations (transpose, permutation, blocks) ********)
(*****************************************************************************)

Section MatrixStructural.

Variable R : Type.

(* Constant matrix *)
Fact const_mx_key : unit.
Proof.
Admitted.
Definition const_mx m n a : 'M[R]_(m, n) := \matrix[const_mx_key]_(i, j) a.
Arguments const_mx {m n}.

Section FixedDim.
(* Definitions and properties for which we can work with fixed dimensions. *)

Variables m n : nat.
Implicit Type A : 'M[R]_(m, n).

(* Reshape a matrix, to accommodate the block functions for instance. *)
Definition castmx m' n' (eq_mn : (m = m') * (n = n')) A : 'M_(m', n') :=
  let: erefl in _ = m' := eq_mn.1 return 'M_(m', n') in
  let: erefl in _ = n' := eq_mn.2 return 'M_(m, n') in A.

Definition conform_mx m' n' B A :=
  match m =P m', n =P n' with
  | ReflectT eq_m, ReflectT eq_n => castmx (eq_m, eq_n) A
  | _, _ => B
  end.

(* Transpose a matrix *)
Fact trmx_key : unit.
Proof.
Admitted.
Definition trmx A := \matrix[trmx_key]_(i, j) A j i.

(* Permute a matrix vertically (rows) or horizontally (columns) *)
Fact row_perm_key : unit.
Proof.
Admitted.
Definition row_perm (s : 'S_m) A := \matrix[row_perm_key]_(i, j) A (s i) j.
Fact col_perm_key : unit.
Proof.
Admitted.
Definition col_perm (s : 'S_n) A := \matrix[col_perm_key]_(i, j) A i (s j).

(* Exchange two rows/columns of a matrix *)
Definition xrow i1 i2 := row_perm (tperm i1 i2).
Definition xcol j1 j2 := col_perm (tperm j1 j2).

(* Row/Column sub matrices of a matrix *)
Definition row i0 A := \row_j A i0 j.
Definition col j0 A := \col_i A i j0.

(* Removing a row/column from a matrix *)
Definition row' i0 A := \matrix_(i, j) A (lift i0 i) j.
Definition col' j0 A := \matrix_(i, j) A i (lift j0 j).

(* reindexing/subindex a matrix *)
Definition mxsub m' n' f g A := \matrix_(i < m', j < n') A (f i) (g j).
Local Notation colsub g := (mxsub id g).
Local Notation rowsub f := (mxsub f id).

Lemma castmx_const m' n' (eq_mn : (m = m') * (n = n')) a :
  castmx eq_mn (const_mx a) = const_mx a.
Proof.
Admitted.

Lemma trmx_const a : trmx (const_mx a) = const_mx a.
Proof.
Admitted.

Lemma row_perm_const s a : row_perm s (const_mx a) = const_mx a.
Proof.
Admitted.

Lemma col_perm_const s a : col_perm s (const_mx a) = const_mx a.
Proof.
Admitted.

Lemma xrow_const i1 i2 a : xrow i1 i2 (const_mx a) = const_mx a.
Proof.
Admitted.

Lemma xcol_const j1 j2 a : xcol j1 j2 (const_mx a) = const_mx a.
Proof.
Admitted.

Lemma rowP (u v : 'rV[R]_n) : u 0 =1 v 0 <-> u = v.
Proof.
Admitted.

Lemma rowK u_ i0 : row i0 (\matrix_i u_ i) = u_ i0.
Proof.
Admitted.

Lemma row_matrixP A B : (forall i, row i A = row i B) <-> A = B.
Proof.
Admitted.

Lemma colP (u v : 'cV[R]_m) : u^~ 0 =1 v^~ 0 <-> u = v.
Proof.
Admitted.

Lemma row_const i0 a : row i0 (const_mx a) = const_mx a.
Proof.
Admitted.

Lemma col_const j0 a : col j0 (const_mx a) = const_mx a.
Proof.
Admitted.

Lemma row'_const i0 a : row' i0 (const_mx a) = const_mx a.
Proof.
Admitted.

Lemma col'_const j0 a : col' j0 (const_mx a) = const_mx a.
Proof.
Admitted.

Lemma col_perm1 A : col_perm 1 A = A.
Proof.
Admitted.

Lemma row_perm1 A : row_perm 1 A = A.
Proof.
Admitted.

Lemma col_permM s t A : col_perm (s * t) A = col_perm s (col_perm t A).
Proof.
Admitted.

Lemma row_permM s t A : row_perm (s * t) A = row_perm s (row_perm t A).
Proof.
Admitted.

Lemma col_row_permC s t A :
  col_perm s (row_perm t A) = row_perm t (col_perm s A).
Proof.
Admitted.

Lemma rowEsub i : row i = rowsub (fun=> i).
Proof.
Admitted.
Lemma colEsub j : col j = colsub (fun=> j).
Proof.
Admitted.

Lemma row'Esub i : row' i = rowsub (lift i).
Proof.
Admitted.
Lemma col'Esub j : col' j = colsub (lift j).
Proof.
Admitted.

Lemma row_permEsub s : row_perm s = rowsub s.
Proof.
Admitted.

Lemma col_permEsub s : col_perm s = colsub s.
Proof.
Admitted.

Lemma xrowEsub i1 i2 : xrow i1 i2 = rowsub (tperm i1 i2).
Proof.
Admitted.

Lemma xcolEsub j1 j2 : xcol j1 j2 = colsub (tperm j1 j2).
Proof.
Admitted.

Lemma mxsub_id : mxsub id id =1 id.
Proof.
Admitted.

Lemma eq_mxsub m' n' f f' g g' : f =1 f' -> g =1 g' ->
  @mxsub m' n' f g =1 mxsub f' g'.
Proof.
Admitted.

Lemma eq_rowsub m' (f f' : 'I_m' -> 'I_m) : f =1 f' -> rowsub f =1 rowsub f'.
Proof.
Admitted.

Lemma eq_colsub n' (g g' : 'I_n' -> 'I_n) : g =1 g' -> colsub g =1 colsub g'.
Proof.
Admitted.

Lemma mxsub_eq_id f g : f =1 id -> g =1 id -> mxsub f g =1 id.
Proof.
Admitted.

Lemma mxsub_eq_colsub n' f g : f =1 id -> @mxsub _ n' f g =1 colsub g.
Proof.
Admitted.

Lemma mxsub_eq_rowsub m' f g : g =1 id -> @mxsub m' _ f g =1 rowsub f.
Proof.
Admitted.

Lemma mxsub_ffunl m' n' f g : @mxsub m' n' (finfun f) g =1 mxsub f g.
Proof.
Admitted.

Lemma mxsub_ffunr m' n' f g : @mxsub m' n' f (finfun g) =1 mxsub f g.
Proof.
Admitted.

Lemma mxsub_ffun m' n' f g : @mxsub m' n' (finfun f) (finfun g) =1 mxsub f g.
Proof.
Admitted.

Lemma mxsub_const m' n' f g a : @mxsub m' n' f g (const_mx a) = const_mx a.
Proof.
Admitted.

End FixedDim.

Local Notation colsub g := (mxsub id g).
Local Notation rowsub f := (mxsub f id).
Local Notation "A ^T" := (trmx A) : ring_scope.

Lemma castmx_id m n erefl_mn (A : 'M_(m, n)) : castmx erefl_mn A = A.
Proof.
Admitted.

Lemma castmx_comp m1 n1 m2 n2 m3 n3 (eq_m1 : m1 = m2) (eq_n1 : n1 = n2)
                                    (eq_m2 : m2 = m3) (eq_n2 : n2 = n3) A :
  castmx (eq_m2, eq_n2) (castmx (eq_m1, eq_n1) A)
    = castmx (etrans eq_m1 eq_m2, etrans eq_n1 eq_n2) A.
Proof.
Admitted.

Lemma castmxK m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) :
  cancel (castmx (eq_m, eq_n)) (castmx (esym eq_m, esym eq_n)).
Proof.
Admitted.

Lemma castmxKV m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) :
  cancel (castmx (esym eq_m, esym eq_n)) (castmx (eq_m, eq_n)).
Proof.
Admitted.

(* This can be use to reverse an equation that involves a cast. *)
Lemma castmx_sym m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) A1 A2 :
  A1 = castmx (eq_m, eq_n) A2 -> A2 = castmx (esym eq_m, esym eq_n) A1.
Proof.
Admitted.

Lemma eq_castmx m1 n1 m2 n2 (eq_mn eq_mn' : (m1 = m2) * (n1 = n2)) :
  castmx eq_mn =1 castmx eq_mn'.
Proof.
Admitted.

Lemma castmxE m1 n1 m2 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A i j :
  castmx eq_mn A i j =
     A (cast_ord (esym eq_mn.
Proof.
Admitted.

Lemma conform_mx_id m n (B A : 'M_(m, n)) : conform_mx B A = A.
Proof.
Admitted.

Lemma nonconform_mx m m' n n' (B : 'M_(m', n')) (A : 'M_(m, n)) :
  (m != m') || (n != n') -> conform_mx B A = B.
Proof.
Admitted.

Lemma conform_castmx m1 n1 m2 n2 m3 n3
                     (e_mn : (m2 = m3) * (n2 = n3)) (B : 'M_(m1, n1)) A :
  conform_mx B (castmx e_mn A) = conform_mx B A.
Proof.
Admitted.

Lemma trmxK m n : cancel (@trmx m n) (@trmx n m).
Proof.
Admitted.

Lemma trmx_inj m n : injective (@trmx m n).
Proof.
Admitted.

Lemma trmx_cast m1 n1 m2 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A :
  (castmx eq_mn A)^T = castmx (eq_mn.
Proof.
Admitted.

Lemma trmx_conform m' n' m n (B : 'M_(m', n')) (A : 'M_(m, n)) :
  (conform_mx B A)^T = conform_mx B^T A^T.
Proof.
Admitted.

Lemma tr_row_perm m n s (A : 'M_(m, n)) : (row_perm s A)^T = col_perm s A^T.
Proof.
Admitted.

Lemma tr_col_perm m n s (A : 'M_(m, n)) : (col_perm s A)^T = row_perm s A^T.
Proof.
Admitted.

Lemma tr_xrow m n i1 i2 (A : 'M_(m, n)) : (xrow i1 i2 A)^T = xcol i1 i2 A^T.
Proof.
Admitted.

Lemma tr_xcol m n j1 j2 (A : 'M_(m, n)) : (xcol j1 j2 A)^T = xrow j1 j2 A^T.
Proof.
Admitted.

Lemma row_id n i (V : 'rV_n) : row i V = V.
Proof.
Admitted.

Lemma col_id n j (V : 'cV_n) : col j V = V.
Proof.
Admitted.

Lemma row_eq m1 m2 n i1 i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  row i1 A1 = row i2 A2 -> A1 i1 =1 A2 i2.
Proof.
Admitted.

Lemma col_eq m n1 n2 j1 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  col j1 A1 = col j2 A2 -> A1^~ j1 =1 A2^~ j2.
Proof.
Admitted.

Lemma row'_eq m n i0 (A B : 'M_(m, n)) :
  row' i0 A = row' i0 B -> {in predC1 i0, A =2 B}.
Proof.
Admitted.

Lemma col'_eq m n j0 (A B : 'M_(m, n)) :
  col' j0 A = col' j0 B -> forall i, {in predC1 j0, A i =1 B i}.
Proof.
Admitted.

Lemma tr_row m n i0 (A : 'M_(m, n)) : (row i0 A)^T = col i0 A^T.
Proof.
Admitted.

Lemma tr_row' m n i0 (A : 'M_(m, n)) : (row' i0 A)^T = col' i0 A^T.
Proof.
Admitted.

Lemma tr_col m n j0 (A : 'M_(m, n)) : (col j0 A)^T = row j0 A^T.
Proof.
Admitted.

Lemma tr_col' m n j0 (A : 'M_(m, n)) : (col' j0 A)^T = row' j0 A^T.
Proof.
Admitted.

Lemma mxsub_comp m1 m2 m3 n1 n2 n3
  (f : 'I_m2 -> 'I_m1) (f' : 'I_m3 -> 'I_m2)
  (g : 'I_n2 -> 'I_n1) (g' : 'I_n3 -> 'I_n2) (A : 'M_(m1, n1)) :
  mxsub (f \o f') (g \o g') A = mxsub f' g' (mxsub f g A).
Proof.
Admitted.

Lemma rowsub_comp m1 m2 m3 n
  (f : 'I_m2 -> 'I_m1) (f' : 'I_m3 -> 'I_m2) (A : 'M_(m1, n)) :
  rowsub (f \o f') A = rowsub f' (rowsub f A).
Proof.
Admitted.

Lemma colsub_comp m n n2 n3
  (g : 'I_n2 -> 'I_n) (g' : 'I_n3 -> 'I_n2) (A : 'M_(m, n)) :
  colsub (g \o g') A = colsub g' (colsub g A).
Proof.
Admitted.

Lemma mxsubrc m1 m2 n n2 f g (A : 'M_(m1, n)) :
  mxsub f g A = rowsub f (colsub g A) :> 'M_(m2, n2).
Proof.
Admitted.

Lemma mxsubcr m1 m2 n n2 f g (A : 'M_(m1, n)) :
  mxsub f g A = colsub g (rowsub f A) :> 'M_(m2, n2).
Proof.
Admitted.

Lemma rowsub_cast m1 m2 n (eq_m : m1 = m2) (A : 'M_(m2, n)) :
  rowsub (cast_ord eq_m) A = castmx (esym eq_m, erefl) A.
Proof.
Admitted.

Lemma colsub_cast m n1 n2 (eq_n : n1 = n2) (A : 'M_(m, n2)) :
  colsub (cast_ord eq_n) A = castmx (erefl, esym eq_n) A.
Proof.
Admitted.

Lemma mxsub_cast m1 m2 n1 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) A :
  mxsub (cast_ord eq_m) (cast_ord eq_n) A = castmx (esym eq_m, esym eq_n) A.
Proof.
Admitted.

Lemma castmxEsub m1 m2 n1 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A :
  castmx eq_mn A = mxsub (cast_ord (esym eq_mn.
Proof.
Admitted.

Lemma trmx_mxsub m1 m2 n1 n2 f g (A : 'M_(m1, n1)) :
  (mxsub f g A)^T = mxsub g f A^T :> 'M_(n2, m2).
Proof.
Admitted.

Lemma row_mxsub m1 m2 n1 n2
    (f : 'I_m2 -> 'I_m1) (g : 'I_n2 -> 'I_n1) (A : 'M_(m1, n1)) i :
  row i (mxsub f g A) = row (f i) (colsub g A).
Proof.
Admitted.

Lemma col_mxsub m1 m2 n1 n2
    (f : 'I_m2 -> 'I_m1) (g : 'I_n2 -> 'I_n1) (A : 'M_(m1, n1)) i :
 col i (mxsub f g A) = col (g i) (rowsub f A).
Proof.
Admitted.

Lemma row_rowsub m1 m2 n (f : 'I_m2 -> 'I_m1) (A : 'M_(m1, n)) i :
  row i (rowsub f A) = row (f i) A.
Proof.
Admitted.

Lemma col_colsub m n1 n2 (g : 'I_n2 -> 'I_n1) (A : 'M_(m, n1)) i :
  col i (colsub g A) = col (g i) A.
Proof.
Admitted.

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

Section CutPaste.

Variables m m1 m2 n n1 n2 : nat.

(* Concatenating two matrices, in either direction. *)

Fact row_mx_key : unit.
Proof.
Admitted.
Definition row_mx (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) : 'M[R]_(m, n1 + n2) :=
  \matrix[row_mx_key]_(i, j)
     match split j with inl j1 => A1 i j1 | inr j2 => A2 i j2 end.

Fact col_mx_key : unit.
Proof.
Admitted.
Definition col_mx (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) : 'M[R]_(m1 + m2, n) :=
  \matrix[col_mx_key]_(i, j)
     match split i with inl i1 => A1 i1 j | inr i2 => A2 i2 j end.

(* Left/Right | Up/Down submatrices of a rows | columns matrix.   *)
(* The shape of the (dependent) width parameters of the type of A *)
(* determines which submatrix is selected.                        *)

Fact lsubmx_key : unit.
Proof.
Admitted.
Definition lsubmx (A : 'M[R]_(m, n1 + n2)) :=
  \matrix[lsubmx_key]_(i, j) A i (lshift n2 j).

Fact rsubmx_key : unit.
Proof.
Admitted.
Definition rsubmx (A : 'M[R]_(m, n1 + n2)) :=
  \matrix[rsubmx_key]_(i, j) A i (rshift n1 j).

Fact usubmx_key : unit.
Proof.
Admitted.
Definition usubmx (A : 'M[R]_(m1 + m2, n)) :=
  \matrix[usubmx_key]_(i, j) A (lshift m2 i) j.

Fact dsubmx_key : unit.
Proof.
Admitted.
Definition dsubmx (A : 'M[R]_(m1 + m2, n)) :=
  \matrix[dsubmx_key]_(i, j) A (rshift m1 i) j.

Lemma row_mxEl A1 A2 i j : row_mx A1 A2 i (lshift n2 j) = A1 i j.
Proof.
Admitted.

Lemma row_mxKl A1 A2 : lsubmx (row_mx A1 A2) = A1.
Proof.
Admitted.

Lemma row_mxEr A1 A2 i j : row_mx A1 A2 i (rshift n1 j) = A2 i j.
Proof.
Admitted.

Lemma row_mxKr A1 A2 : rsubmx (row_mx A1 A2) = A2.
Proof.
Admitted.

Lemma hsubmxK A : row_mx (lsubmx A) (rsubmx A) = A.
Proof.
Admitted.

Lemma col_mxEu A1 A2 i j : col_mx A1 A2 (lshift m2 i) j = A1 i j.
Proof.
Admitted.

Lemma col_mxKu A1 A2 : usubmx (col_mx A1 A2) = A1.
Proof.
Admitted.

Lemma col_mxEd A1 A2 i j : col_mx A1 A2 (rshift m1 i) j = A2 i j.
Proof.
Admitted.

Lemma col_mxKd A1 A2 : dsubmx (col_mx A1 A2) = A2.
Proof.
Admitted.

Lemma lsubmxEsub : lsubmx = colsub (lshift _).
Proof.
Admitted.

Lemma rsubmxEsub : rsubmx = colsub (@rshift _ _).
Proof.
Admitted.

Lemma usubmxEsub : usubmx = rowsub (lshift _).
Proof.
Admitted.

Lemma dsubmxEsub  : dsubmx = rowsub (@rshift _ _).
Proof.
Admitted.

Lemma eq_row_mx A1 A2 B1 B2 : row_mx A1 A2 = row_mx B1 B2 -> A1 = B1 /\ A2 = B2.
Proof.
Admitted.

Lemma eq_col_mx A1 A2 B1 B2 : col_mx A1 A2 = col_mx B1 B2 -> A1 = B1 /\ A2 = B2.
Proof.
Admitted.

Lemma lsubmx_const (r : R) : lsubmx (const_mx r : 'M_(m, n1 + n2)) = const_mx r.
Proof.
Admitted.

Lemma rsubmx_const (r : R) : rsubmx (const_mx r : 'M_(m, n1 + n2)) = const_mx r.
Proof.
Admitted.

Lemma row_mx_const a : row_mx (const_mx a) (const_mx a) = const_mx a.
Proof.
Admitted.

Lemma col_mx_const a : col_mx (const_mx a) (const_mx a) = const_mx a.
Proof.
Admitted.

Lemma row_usubmx A i : row i (usubmx A) = row (lshift m2 i) A.
Proof.
Admitted.

Lemma row_dsubmx A i : row i (dsubmx A) = row (rshift m1 i) A.
Proof.
Admitted.

Lemma col_lsubmx A i : col i (lsubmx A) = col (lshift n2 i) A.
Proof.
Admitted.

Lemma col_rsubmx A i : col i (rsubmx A) = col (rshift n1 i) A.
Proof.
Admitted.

End CutPaste.

Lemma row_thin_mx m n (A : 'M_(m,0)) (B : 'M_(m,n)) : row_mx A B = B.
Proof.
Admitted.

Lemma col_flat_mx m n (A : 'M_(0,n)) (B : 'M_(m,n)) : col_mx A B = B.
Proof.
Admitted.

Lemma trmx_lsub m n1 n2 (A : 'M_(m, n1 + n2)) : (lsubmx A)^T = usubmx A^T.
Proof.
Admitted.

Lemma trmx_rsub m n1 n2 (A : 'M_(m, n1 + n2)) : (rsubmx A)^T = dsubmx A^T.
Proof.
Admitted.

Lemma tr_row_mx m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  (row_mx A1 A2)^T = col_mx A1^T A2^T.
Proof.
Admitted.

Lemma tr_col_mx m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  (col_mx A1 A2)^T = row_mx A1^T A2^T.
Proof.
Admitted.

Lemma trmx_usub m1 m2 n (A : 'M_(m1 + m2, n)) : (usubmx A)^T = lsubmx A^T.
Proof.
Admitted.

Lemma trmx_dsub m1 m2 n (A : 'M_(m1 + m2, n)) : (dsubmx A)^T = rsubmx A^T.
Proof.
Admitted.

Lemma vsubmxK m1 m2 n (A : 'M_(m1 + m2, n)) : col_mx (usubmx A) (dsubmx A) = A.
Proof.
Admitted.

Lemma cast_row_mx m m' n1 n2 (eq_m : m = m') A1 A2 :
  castmx (eq_m, erefl _) (row_mx A1 A2)
    = row_mx (castmx (eq_m, erefl n1) A1) (castmx (eq_m, erefl n2) A2).
Proof.
Admitted.

Lemma cast_col_mx m1 m2 n n' (eq_n : n = n') A1 A2 :
  castmx (erefl _, eq_n) (col_mx A1 A2)
    = col_mx (castmx (erefl m1, eq_n) A1) (castmx (erefl m2, eq_n) A2).
Proof.
Admitted.

(* This lemma has Prenex Implicits to help RL rewriting with castmx_sym. *)
Lemma row_mxA m n1 n2 n3 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) (A3 : 'M_(m, n3)) :
  let cast := (erefl m, esym (addnA n1 n2 n3)) in
  row_mx A1 (row_mx A2 A3) = castmx cast (row_mx (row_mx A1 A2) A3).
Proof.
Admitted.
Definition row_mxAx := row_mxA. (* bypass Prenex Implicits. *)

(* This lemma has Prenex Implicits to help RL rewrititng with castmx_sym. *)
Lemma col_mxA m1 m2 m3 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) (A3 : 'M_(m3, n)) :
  let cast := (esym (addnA m1 m2 m3), erefl n) in
  col_mx A1 (col_mx A2 A3) = castmx cast (col_mx (col_mx A1 A2) A3).
Proof.
Admitted.
Definition col_mxAx := col_mxA. (* bypass Prenex Implicits. *)

Lemma row_row_mx m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  row i0 (row_mx A1 A2) = row_mx (row i0 A1) (row i0 A2).
Proof.
Admitted.

Lemma col_col_mx m1 m2 n j0 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  col j0 (col_mx A1 A2) = col_mx (col j0 A1) (col j0 A2).
Proof.
Admitted.

Lemma row'_row_mx m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  row' i0 (row_mx A1 A2) = row_mx (row' i0 A1) (row' i0 A2).
Proof.
Admitted.

Lemma col'_col_mx m1 m2 n j0 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  col' j0 (col_mx A1 A2) = col_mx (col' j0 A1) (col' j0 A2).
Proof.
Admitted.

Lemma colKl m n1 n2 j1 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  col (lshift n2 j1) (row_mx A1 A2) = col j1 A1.
Proof.
Admitted.

Lemma colKr m n1 n2 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  col (rshift n1 j2) (row_mx A1 A2) = col j2 A2.
Proof.
Admitted.

Lemma rowKu m1 m2 n i1 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  row (lshift m2 i1) (col_mx A1 A2) = row i1 A1.
Proof.
Admitted.

Lemma rowKd m1 m2 n i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  row (rshift m1 i2) (col_mx A1 A2) = row i2 A2.
Proof.
Admitted.

Lemma col'Kl m n1 n2 j1 (A1 : 'M_(m, n1.
Proof.
Admitted.

Lemma row'Ku m1 m2 n i1 (A1 : 'M_(m1.
Proof.
Admitted.

Lemma mx'_cast m n : 'I_n -> (m + n.
Proof.
Admitted.

Lemma col'Kr m n1 n2 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  col' (rshift n1 j2) (@row_mx m n1 n2 A1 A2)
    = castmx (erefl m, mx'_cast n1 j2) (row_mx A1 (col' j2 A2)).
Proof.
Admitted.

Lemma row'Kd m1 m2 n i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  row' (rshift m1 i2) (col_mx A1 A2)
    = castmx (mx'_cast m1 i2, erefl n) (col_mx A1 (row' i2 A2)).
Proof.
Admitted.

Section Block.

Variables m1 m2 n1 n2 : nat.

(* Building a block matrix from 4 matrices :               *)
(*  up left, up right, down left and down right components *)

Definition block_mx Aul Aur Adl Adr : 'M_(m1 + m2, n1 + n2) :=
  col_mx (row_mx Aul Aur) (row_mx Adl Adr).

Lemma eq_block_mx Aul Aur Adl Adr Bul Bur Bdl Bdr :
 block_mx Aul Aur Adl Adr = block_mx Bul Bur Bdl Bdr ->
  [/\ Aul = Bul, Aur = Bur, Adl = Bdl & Adr = Bdr].
Proof.
Admitted.

Lemma block_mx_const a :
  block_mx (const_mx a) (const_mx a) (const_mx a) (const_mx a) = const_mx a.
Proof.
Admitted.

Section CutBlock.

Variable A : matrix R (m1 + m2) (n1 + n2).

Definition ulsubmx := lsubmx (usubmx A).
Definition ursubmx := rsubmx (usubmx A).
Definition dlsubmx := lsubmx (dsubmx A).
Definition drsubmx := rsubmx (dsubmx A).

Lemma submxK : block_mx ulsubmx ursubmx dlsubmx drsubmx = A.
Proof.
Admitted.

Lemma ulsubmxEsub : ulsubmx = mxsub (lshift _) (lshift _) A.
Proof.
Admitted.

Lemma dlsubmxEsub : dlsubmx = mxsub (@rshift _ _) (lshift _) A.
Proof.
Admitted.

Lemma ursubmxEsub : ursubmx = mxsub (lshift _) (@rshift _ _) A.
Proof.
Admitted.

Lemma drsubmxEsub : drsubmx = mxsub (@rshift _ _) (@rshift _ _) A.
Proof.
Admitted.

End CutBlock.

Section CatBlock.

Variables (Aul : 'M[R]_(m1, n1)) (Aur : 'M[R]_(m1, n2)).
Variables (Adl : 'M[R]_(m2, n1)) (Adr : 'M[R]_(m2, n2)).

Let A := block_mx Aul Aur Adl Adr.

Lemma block_mxEul i j : A (lshift m2 i) (lshift n2 j) = Aul i j.
Proof.
Admitted.
Lemma block_mxKul : ulsubmx A = Aul.
Proof.
Admitted.

Lemma block_mxEur i j : A (lshift m2 i) (rshift n1 j) = Aur i j.
Proof.
Admitted.
Lemma block_mxKur : ursubmx A = Aur.
Proof.
Admitted.

Lemma block_mxEdl i j : A (rshift m1 i) (lshift n2 j) = Adl i j.
Proof.
Admitted.
Lemma block_mxKdl : dlsubmx A = Adl.
Proof.
Admitted.

Lemma block_mxEdr i j : A (rshift m1 i) (rshift n1 j) = Adr i j.
Proof.
Admitted.
Lemma block_mxKdr : drsubmx A = Adr.
Proof.
Admitted.

Lemma block_mxEv : A = col_mx (row_mx Aul Aur) (row_mx Adl Adr).
Proof.
Admitted.

End CatBlock.

End Block.

Section TrCutBlock.

Variables m1 m2 n1 n2 : nat.
Variable A : 'M[R]_(m1 + m2, n1 + n2).

Lemma trmx_ulsub : (ulsubmx A)^T = ulsubmx A^T.
Proof.
Admitted.

Lemma trmx_ursub : (ursubmx A)^T = dlsubmx A^T.
Proof.
Admitted.

Lemma trmx_dlsub : (dlsubmx A)^T = ursubmx A^T.
Proof.
Admitted.

Lemma trmx_drsub : (drsubmx A)^T = drsubmx A^T.
Proof.
Admitted.

End TrCutBlock.

Section TrBlock.
Variables m1 m2 n1 n2 : nat.
Variables (Aul : 'M[R]_(m1, n1)) (Aur : 'M[R]_(m1, n2)).
Variables (Adl : 'M[R]_(m2, n1)) (Adr : 'M[R]_(m2, n2)).

Lemma tr_block_mx :
 (block_mx Aul Aur Adl Adr)^T = block_mx Aul^T Adl^T Aur^T Adr^T.
Proof.
Admitted.

Lemma block_mxEh :
  block_mx Aul Aur Adl Adr = row_mx (col_mx Aul Adl) (col_mx Aur Adr).
Proof.
Admitted.
End TrBlock.

(* This lemma has Prenex Implicits to help RL rewrititng with castmx_sym. *)
Lemma block_mxA m1 m2 m3 n1 n2 n3
   (A11 : 'M_(m1, n1)) (A12 : 'M_(m1, n2)) (A13 : 'M_(m1, n3))
   (A21 : 'M_(m2, n1)) (A22 : 'M_(m2, n2)) (A23 : 'M_(m2, n3))
   (A31 : 'M_(m3, n1)) (A32 : 'M_(m3, n2)) (A33 : 'M_(m3, n3)) :
  let cast := (esym (addnA m1 m2 m3), esym (addnA n1 n2 n3)) in
  let row1 := row_mx A12 A13 in let col1 := col_mx A21 A31 in
  let row3 := row_mx A31 A32 in let col3 := col_mx A13 A23 in
  block_mx A11 row1 col1 (block_mx A22 A23 A32 A33)
    = castmx cast (block_mx (block_mx A11 A12 A21 A22) col3 row3 A33).
Proof.
Admitted.
Definition block_mxAx := block_mxA. (* Bypass Prenex Implicits *)

Section Induction.

Lemma row_ind m (P : forall n, 'M[R]_(m, n) -> Type) :
    (forall A, P 0 A) ->
    (forall n c A, P n A -> P (1 + n)%N (row_mx c A)) ->
  forall n A, P n A.
Proof.
Admitted.

Lemma col_ind n (P : forall m, 'M[R]_(m, n) -> Type) :
    (forall A, P 0 A) ->
    (forall m r A, P m A -> P (1 + m)%N (col_mx r A)) ->
  forall m A, P m A.
Proof.
Admitted.

Lemma mx_ind (P : forall m n, 'M[R]_(m, n) -> Type) :
    (forall m A, P m 0 A) ->
    (forall n A, P 0 n A) ->
    (forall m n x r c A, P m n A -> P (1 + m)%N (1 + n)%N (block_mx x r c A)) ->
  forall m n A, P m n A.
Proof.
Admitted.
Definition matrix_rect := mx_ind.
Definition matrix_rec := mx_ind.
Definition matrix_ind := mx_ind.

Lemma sqmx_ind (P : forall n, 'M[R]_n -> Type) :
    (forall A, P 0 A) ->
    (forall n x r c A, P n A -> P (1 + n)%N (block_mx x r c A)) ->
  forall n A, P n A.
Proof.
Admitted.

Lemma ringmx_ind (P : forall n, 'M[R]_n.
Proof.
Admitted.

Lemma mxsub_ind
    (weight : forall m n, 'M[R]_(m, n) -> nat)
    (sub : forall m n m' n', ('I_m' -> 'I_m) -> ('I_n' -> 'I_n) -> Prop)
    (P : forall m n, 'M[R]_(m, n) -> Type) :
    (forall m n (A : 'M[R]_(m, n)),
      (forall m' n' f g, weight m' n' (mxsub f g A) < weight m n A ->
                         sub m n m' n' f g ->
                         P m' n' (mxsub f g A)) -> P m n A) ->
  forall m n A, P m n A.
Proof.
Admitted.

End Induction.

(* Bijections mxvec : 'M_(m, n) <----> 'rV_(m * n) : vec_mx *)
Section VecMatrix.

Variables m n : nat.

Lemma mxvec_cast : #|{:'I_m * 'I_n}| = (m * n)%N.
Proof.
Admitted.

Definition mxvec_index (i : 'I_m) (j : 'I_n) :=
  cast_ord mxvec_cast (enum_rank (i, j)).

Variant is_mxvec_index : 'I_(m * n) -> Type :=
  isMxvecIndex i j : is_mxvec_index (mxvec_index i j).

Lemma mxvec_indexP k : is_mxvec_index k.
Proof.
Admitted.

Coercion pair_of_mxvec_index k (i_k : is_mxvec_index k) :=
  let: isMxvecIndex i j := i_k in (i, j).

Definition mxvec (A : 'M[R]_(m, n)) :=
  castmx (erefl _, mxvec_cast) (\row_k A (enum_val k).1 (enum_val k).2).

Fact vec_mx_key : unit.
Proof.
Admitted.
Definition vec_mx (u : 'rV[R]_(m * n)) :=
  \matrix[vec_mx_key]_(i, j) u 0 (mxvec_index i j).

Lemma mxvecE A i j : mxvec A 0 (mxvec_index i j) = A i j.
Proof.
Admitted.

Lemma mxvecK : cancel mxvec vec_mx.
Proof.
Admitted.

Lemma vec_mxK : cancel vec_mx mxvec.
Proof.
Admitted.

Lemma curry_mxvec_bij : {on 'I_(m * n), bijective (uncurry mxvec_index)}.
Proof.
Admitted.

End VecMatrix.

End MatrixStructural.

Arguments const_mx {R m n}.
Arguments row_mxA {R m n1 n2 n3 A1 A2 A3}.
Arguments col_mxA {R m1 m2 m3 n A1 A2 A3}.
Arguments block_mxA {R m1 m2 m3 n1 n2 n3 A11 A12 A13 A21 A22 A23 A31 A32 A33}.
Prenex Implicits castmx trmx trmxK lsubmx rsubmx usubmx dsubmx row_mx col_mx.
Prenex Implicits block_mx ulsubmx ursubmx dlsubmx drsubmx.
Prenex Implicits mxvec vec_mx mxvec_indexP mxvecK vec_mxK.
Arguments trmx_inj {R m n} [A1 A2] eqA12t : rename.

Notation "A ^T" := (trmx A) : ring_scope.
Notation colsub g := (mxsub id g).
Notation rowsub f := (mxsub f id).

Arguments eq_mxsub [R m n m' n' f] f' [g] g' _.
Arguments eq_rowsub [R m n m' f] f' _.
Arguments eq_colsub [R m n n' g] g' _.

(* Matrix parametricity. *)
Section MapMatrix.

Variables (aT rT : Type) (f : aT -> rT).

Fact map_mx_key : unit.
Proof.
Admitted.
Definition map_mx m n (A : 'M_(m, n)) := \matrix[map_mx_key]_(i, j) f (A i j).

Notation "A ^f" := (map_mx A) : ring_scope.

Section OneMatrix.

Variables (m n : nat) (A : 'M[aT]_(m, n)).

Lemma map_trmx : A^f^T = A^T^f.
Proof.
Admitted.

Lemma map_const_mx a : (const_mx a)^f = const_mx (f a) :> 'M_(m, n).
Proof.
Admitted.

Lemma map_row i : (row i A)^f = row i A^f.
Proof.
Admitted.

Lemma map_col j : (col j A)^f = col j A^f.
Proof.
Admitted.

Lemma map_row' i0 : (row' i0 A)^f = row' i0 A^f.
Proof.
Admitted.

Lemma map_col' j0 : (col' j0 A)^f = col' j0 A^f.
Proof.
Admitted.

Lemma map_mxsub m' n' g h : (@mxsub _ _ _  m' n' g h A)^f = mxsub g h A^f.
Proof.
Admitted.

Lemma map_row_perm s : (row_perm s A)^f = row_perm s A^f.
Proof.
Admitted.

Lemma map_col_perm s : (col_perm s A)^f = col_perm s A^f.
Proof.
Admitted.

Lemma map_xrow i1 i2 : (xrow i1 i2 A)^f = xrow i1 i2 A^f.
Proof.
Admitted.

Lemma map_xcol j1 j2 : (xcol j1 j2 A)^f = xcol j1 j2 A^f.
Proof.
Admitted.

Lemma map_castmx m' n' c : (castmx c A)^f = castmx c A^f :> 'M_(m', n').
Proof.
Admitted.

Lemma map_conform_mx m' n' (B : 'M_(m', n')) :
  (conform_mx B A)^f = conform_mx B^f A^f.
Proof.
Admitted.

Lemma map_mxvec : (mxvec A)^f = mxvec A^f.
Proof.
Admitted.

Lemma map_vec_mx (v : 'rV_(m * n)) : (vec_mx v)^f = vec_mx v^f.
Proof.
Admitted.

End OneMatrix.

Section Block.

Variables m1 m2 n1 n2 : nat.
Variables (Aul : 'M[aT]_(m1, n1)) (Aur : 'M[aT]_(m1, n2)).
Variables (Adl : 'M[aT]_(m2, n1)) (Adr : 'M[aT]_(m2, n2)).
Variables (Bh : 'M[aT]_(m1, n1 + n2)) (Bv : 'M[aT]_(m1 + m2, n1)).
Variable B : 'M[aT]_(m1 + m2, n1 + n2).

Lemma map_row_mx : (row_mx Aul Aur)^f = row_mx Aul^f Aur^f.
Proof.
Admitted.

Lemma map_col_mx : (col_mx Aul Adl)^f = col_mx Aul^f Adl^f.
Proof.
Admitted.

Lemma map_block_mx :
  (block_mx Aul Aur Adl Adr)^f = block_mx Aul^f Aur^f Adl^f Adr^f.
Proof.
Admitted.

Lemma map_lsubmx : (lsubmx Bh)^f = lsubmx Bh^f.
Proof.
Admitted.

Lemma map_rsubmx : (rsubmx Bh)^f = rsubmx Bh^f.
Proof.
Admitted.

Lemma map_usubmx : (usubmx Bv)^f = usubmx Bv^f.
Proof.
Admitted.

Lemma map_dsubmx : (dsubmx Bv)^f = dsubmx Bv^f.
Proof.
Admitted.

Lemma map_ulsubmx : (ulsubmx B)^f = ulsubmx B^f.
Proof.
Admitted.

Lemma map_ursubmx : (ursubmx B)^f = ursubmx B^f.
Proof.
Admitted.

Lemma map_dlsubmx : (dlsubmx B)^f = dlsubmx B^f.
Proof.
Admitted.

Lemma map_drsubmx : (drsubmx B)^f = drsubmx B^f.
Proof.
Admitted.

End Block.

End MapMatrix.

Arguments map_mx {aT rT} f {m n} A.

Section MultipleMapMatrix.
Context {R S T : Type} {m n : nat}.
Local Notation "M ^ phi" := (map_mx phi M).

Lemma map_mx_comp (f : R -> S) (g : S -> T)
  (M : 'M_(m, n)) : M ^ (g \o f) = (M ^ f) ^ g.
Proof.
Admitted.

Lemma eq_in_map_mx (g f : R -> S) (M : 'M_(m, n)) :
  (forall i j, f (M i j) = g (M i j)) -> M ^ f = M ^ g.
Proof.
Admitted.

Lemma eq_map_mx (g f : R -> S) : f =1 g ->
  forall (M : 'M_(m, n)), M ^ f = M ^ g.
Proof.
Admitted.

Lemma map_mx_id_in (f : R -> R) (M : 'M_(m, n)) :
  (forall i j, f (M i j) = M i j) -> M ^ f = M.
Proof.
Admitted.

Lemma map_mx_id (f : R -> R) : f =1 id -> forall M : 'M_(m, n), M ^ f = M.
Proof.
Admitted.

End MultipleMapMatrix.
Arguments eq_map_mx {R S m n} g [f].
Arguments eq_in_map_mx {R S m n} g [f M].
Arguments map_mx_id_in {R m n} [f M].
Arguments map_mx_id {R m n} [f].

(*****************************************************************************)
(********************* Matrix lifted laws *******************)
(*****************************************************************************)

Section Map2Matrix.
Context {R S T : Type} (f : R -> S -> T).

Fact map2_mx_key : unit.
Proof.
Admitted.
Definition map2_mx m n (A : 'M_(m, n)) (B : 'M_(m, n)) :=
  \matrix[map2_mx_key]_(i, j) f (A i j) (B i j).

Section OneMatrix.

Variables (m n : nat) (A : 'M[R]_(m, n)) (B : 'M[S]_(m, n)).

Lemma map2_trmx : (map2_mx A B)^T = map2_mx A^T B^T.
Proof.
Admitted.

Lemma map2_const_mx a b :
  map2_mx (const_mx a) (const_mx b) = const_mx (f a b) :> 'M_(m, n).
Proof.
Admitted.

Lemma map2_row i : map2_mx (row i A) (row i B) = row i (map2_mx A B).
Proof.
Admitted.

Lemma map2_col j : map2_mx (col j A) (col j B) = col j (map2_mx A B).
Proof.
Admitted.

Lemma map2_row' i0 : map2_mx (row' i0 A) (row' i0 B) = row' i0 (map2_mx A B).
Proof.
Admitted.

Lemma map2_col' j0 : map2_mx (col' j0 A) (col' j0 B) = col' j0 (map2_mx A B).
Proof.
Admitted.

Lemma map2_mxsub m' n' g h :
  map2_mx (@mxsub _ _ _  m' n' g h A) (@mxsub _ _ _  m' n' g h B) =
  mxsub g h (map2_mx A B).
Proof.
Admitted.

Lemma map2_row_perm s :
  map2_mx (row_perm s A) (row_perm s B) = row_perm s (map2_mx A B).
Proof.
Admitted.

Lemma map2_col_perm s :
  map2_mx (col_perm s A) (col_perm s B) = col_perm s (map2_mx A B).
Proof.
Admitted.

Lemma map2_xrow i1 i2 :
  map2_mx (xrow i1 i2 A) (xrow i1 i2 B) = xrow i1 i2 (map2_mx A B).
Proof.
Admitted.

Lemma map2_xcol j1 j2 :
  map2_mx (xcol j1 j2 A) (xcol j1 j2 B) = xcol j1 j2 (map2_mx A B).
Proof.
Admitted.

Lemma map2_castmx m' n' c :
  map2_mx (castmx c A) (castmx c B) = castmx c (map2_mx A B) :> 'M_(m', n').
Proof.
Admitted.

Lemma map2_conform_mx m' n' (A' : 'M_(m', n')) (B' : 'M_(m', n')) :
  map2_mx (conform_mx A' A) (conform_mx B' B) =
  conform_mx (map2_mx A' B') (map2_mx A B).
Proof.
Admitted.

Lemma map2_mxvec : map2_mx (mxvec A) (mxvec B) = mxvec (map2_mx A B).
Proof.
Admitted.

Lemma map2_vec_mx (v : 'rV_(m * n)) (w : 'rV_(m * n)) :
  map2_mx (vec_mx v) (vec_mx w) = vec_mx (map2_mx v w).
Proof.
Admitted.

End OneMatrix.

Section Block.

Variables m1 m2 n1 n2 : nat.
Variables (Aul : 'M[R]_(m1, n1)) (Aur : 'M[R]_(m1, n2)).
Variables (Adl : 'M[R]_(m2, n1)) (Adr : 'M[R]_(m2, n2)).
Variables (Bh : 'M[R]_(m1, n1 + n2)) (Bv : 'M[R]_(m1 + m2, n1)).
Variable B : 'M[R]_(m1 + m2, n1 + n2).
Variables (A'ul : 'M[S]_(m1, n1)) (A'ur : 'M[S]_(m1, n2)).
Variables (A'dl : 'M[S]_(m2, n1)) (A'dr : 'M[S]_(m2, n2)).
Variables (B'h : 'M[S]_(m1, n1 + n2)) (B'v : 'M[S]_(m1 + m2, n1)).
Variable B' : 'M[S]_(m1 + m2, n1 + n2).

Lemma map2_row_mx :
  map2_mx (row_mx Aul Aur) (row_mx A'ul A'ur) =
  row_mx (map2_mx Aul A'ul) (map2_mx Aur A'ur).
Proof.
Admitted.

Lemma map2_col_mx :
  map2_mx (col_mx Aul Adl) (col_mx A'ul A'dl) =
  col_mx (map2_mx Aul A'ul) (map2_mx Adl A'dl).
Proof.
Admitted.

Lemma map2_block_mx :
  map2_mx (block_mx Aul Aur Adl Adr) (block_mx A'ul A'ur A'dl A'dr) =
  block_mx
   (map2_mx Aul A'ul) (map2_mx Aur A'ur) (map2_mx Adl A'dl) (map2_mx Adr A'dr).
Proof.
Admitted.

Lemma map2_lsubmx : map2_mx (lsubmx Bh) (lsubmx B'h) = lsubmx (map2_mx Bh B'h).
Proof.
Admitted.

Lemma map2_rsubmx : map2_mx (rsubmx Bh) (rsubmx B'h) = rsubmx (map2_mx Bh B'h).
Proof.
Admitted.

Lemma map2_usubmx : map2_mx (usubmx Bv) (usubmx B'v) = usubmx (map2_mx Bv B'v).
Proof.
Admitted.

Lemma map2_dsubmx : map2_mx (dsubmx Bv) (dsubmx B'v) = dsubmx (map2_mx Bv B'v).
Proof.
Admitted.

Lemma map2_ulsubmx : map2_mx (ulsubmx B) (ulsubmx B') = ulsubmx (map2_mx B B').
Proof.
Admitted.

Lemma map2_ursubmx : map2_mx (ursubmx B) (ursubmx B') = ursubmx (map2_mx B B').
Proof.
Admitted.

Lemma map2_dlsubmx : map2_mx (dlsubmx B) (dlsubmx B') = dlsubmx (map2_mx B B').
Proof.
Admitted.

Lemma map2_drsubmx : map2_mx (drsubmx B) (drsubmx B') = drsubmx (map2_mx B B').
Proof.
Admitted.

End Block.

End Map2Matrix.

Section Map2Eq.

Context {R S T : Type} {m n : nat}.

Lemma eq_in_map2_mx (f g : R -> S -> T) (M : 'M[R]_(m, n)) (M' : 'M[S]_(m, n)) :
  (forall i j, f (M i j) (M' i j) = g (M i j) (M' i j)) ->
  map2_mx f M M' = map2_mx g M M'.
Proof.
Admitted.

Lemma eq_map2_mx (f g : R -> S -> T) : f =2 g ->
  @map2_mx _ _ _ f m n =2 @map2_mx _ _ _ g m n.
Proof.
Admitted.

Lemma map2_mx_left_in (f : R -> R -> R) (M : 'M_(m, n)) (M' : 'M_(m, n)) :
  (forall i j, f (M i j) (M' i j) = M i j) -> map2_mx f M M' = M.
Proof.
Admitted.

Lemma map2_mx_left (f : R -> R -> R) : f =2 (fun x _ => x) ->
  forall (M : 'M_(m, n)) (M' : 'M_(m, n)), map2_mx f M M' = M.
Proof.
Admitted.

Lemma map2_mx_right_in (f : R -> R -> R) (M : 'M_(m, n)) (M' : 'M_(m, n)) :
  (forall i j, f (M i j) (M' i j) = M' i j) -> map2_mx f M M' = M'.
Proof.
Admitted.

Lemma map2_mx_right (f : R -> R -> R) : f =2 (fun _ x => x) ->
  forall (M : 'M_(m, n)) (M' : 'M_(m, n)), map2_mx f M M' = M'.
Proof.
Admitted.

End Map2Eq.

Section MatrixLaws.

Context {T : Type} {m n : nat} {idm : T}.

Lemma map2_mxA {opm : Monoid.
Proof.
Admitted.

Lemma map2_1mx {opm : Monoid.
Proof.
Admitted.

Lemma map2_mx1 {opm : Monoid.
Proof.
Admitted.

HB.instance Definition _ {opm : Monoid.law idm} :=
  Monoid.isLaw.Build 'M_(m, n) (const_mx idm) (@map2_mx _ _ _ opm _ _)
    map2_mxA map2_1mx map2_mx1.

Lemma map2_mxC {opm : Monoid.
Proof.
Admitted.

HB.instance Definition _ {opm : Monoid.com_law idm} :=
  SemiGroup.isCommutativeLaw.Build 'M_(m, n) (@map2_mx _ _ _ opm _ _) map2_mxC.

Lemma map2_0mx {opm : Monoid.
Proof.
Admitted.

Lemma map2_mx0 {opm : Monoid.
Proof.
Admitted.

HB.instance Definition _ {opm : Monoid.mul_law idm} :=
  Monoid.isMulLaw.Build 'M_(m, n) (const_mx idm) (@map2_mx _ _ _ opm _ _)
    map2_0mx map2_mx0.

Lemma map2_mxDl {mul : T -> T -> T} {add : Monoid.
Proof.
Admitted.

Lemma map2_mxDr {mul : T -> T -> T} {add : Monoid.
Proof.
Admitted.

HB.instance Definition _ {mul : T -> T -> T} {add : Monoid.add_law idm mul} :=
  Monoid.isAddLaw.Build 'M_(m, n)
    (@map2_mx _ _ _ mul _ _) (@map2_mx _ _ _ add _ _)
    map2_mxDl map2_mxDr.

End MatrixLaws.

(*****************************************************************************)
(************* Matrix Nmodule (additive abelian monoid) structure ************)
(*****************************************************************************)

Section MatrixNmodule.

Variable V : nmodType.

Section FixedDim.

Variables m n : nat.
Implicit Types A B : 'M[V]_(m, n).

Fact addmx_key : unit.
Proof.
Admitted.
Definition addmx := @map2_mx V V V +%R m n.

Definition addmxA : associative addmx := map2_mxA.
Definition addmxC : commutative addmx := map2_mxC.
Definition add0mx : left_id (const_mx 0) addmx := map2_1mx.

HB.instance Definition _ := GRing.isNmodule.Build 'M[V]_(m, n)
  addmxA addmxC add0mx.

Lemma mulmxnE A d i j : (A *+ d) i j = A i j *+ d.
Proof.
Admitted.

Lemma summxE I r (P : pred I) (E : I -> 'M_(m, n)) i j :
  (\sum_(k <- r | P k) E k) i j = \sum_(k <- r | P k) E k i j.
Proof.
Admitted.

Fact const_mx_is_nmod_morphism : nmod_morphism const_mx.
Proof.
Admitted.
#[deprecated(since="mathcomp 2.5.0", use=const_mx_is_nmod_morphism)]
Definition const_mx_is_semi_additive := const_mx_is_nmod_morphism.
HB.instance Definition _ := GRing.isNmodMorphism.Build V 'M[V]_(m, n) const_mx
  const_mx_is_nmod_morphism.

End FixedDim.

Section SemiAdditive.

Variables (m n p q : nat) (f : 'I_p -> 'I_q -> 'I_m) (g : 'I_p -> 'I_q -> 'I_n).

Definition swizzle_mx k (A : 'M[V]_(m, n)) :=
  \matrix[k]_(i, j) A (f i j) (g i j).

Fact swizzle_mx_is_nmod_morphism k : nmod_morphism (swizzle_mx k).
Proof.
Admitted.
#[deprecated(since="mathcomp 2.5.0", use=swizzle_mx_is_nmod_morphism)]
Definition swizzle_mx_is_semi_additive := swizzle_mx_is_nmod_morphism.
HB.instance Definition _ k := GRing.isNmodMorphism.Build 'M_(m, n) 'M_(p, q)
  (swizzle_mx k) (swizzle_mx_is_nmod_morphism k).

End SemiAdditive.

Local Notation SwizzleAdd op := (GRing.Additive.copy op (swizzle_mx _ _ _)).

HB.instance Definition _ m n := SwizzleAdd (@trmx V m n).
HB.instance Definition _ m n i := SwizzleAdd (@row V m n i).
HB.instance Definition _ m n j := SwizzleAdd (@col V m n j).
HB.instance Definition _ m n i := SwizzleAdd (@row' V m n i).
HB.instance Definition _ m n j := SwizzleAdd (@col' V m n j).
HB.instance Definition _ m n m' n' f g := SwizzleAdd (@mxsub V m n m' n' f g).
HB.instance Definition _ m n s := SwizzleAdd (@row_perm V m n s).
HB.instance Definition _ m n s := SwizzleAdd (@col_perm V m n s).
HB.instance Definition _ m n i1 i2 := SwizzleAdd (@xrow V m n i1 i2).
HB.instance Definition _ m n j1 j2 := SwizzleAdd (@xcol V m n j1 j2).
HB.instance Definition _ m n1 n2 := SwizzleAdd (@lsubmx V m n1 n2).
HB.instance Definition _ m n1 n2 := SwizzleAdd (@rsubmx V m n1 n2).
HB.instance Definition _ m1 m2 n := SwizzleAdd (@usubmx V m1 m2 n).
HB.instance Definition _ m1 m2 n := SwizzleAdd (@dsubmx V m1 m2 n).
HB.instance Definition _ m n := SwizzleAdd (@vec_mx V m n).
HB.instance Definition _ m n := GRing.isNmodMorphism.Build 'M_(m, n) 'rV_(m * n)
  mxvec (can2_nmod_morphism (@vec_mxK V m n) mxvecK).

Lemma flatmx0 n : all_equal_to (0 : 'M_(0, n)).
Proof.
Admitted.

Lemma thinmx0 n : all_equal_to (0 : 'M_(n, 0)).
Proof.
Admitted.

Lemma trmx0 m n : (0 : 'M_(m, n))^T = 0.
Proof.
Admitted.

Lemma row0 m n i0 : row i0 (0 : 'M_(m, n)) = 0.
Proof.
Admitted.

Lemma col0 m n j0 : col j0 (0 : 'M_(m, n)) = 0.
Proof.
Admitted.

Lemma mxvec_eq0 m n (A : 'M_(m, n)) : (mxvec A == 0) = (A == 0).
Proof.
Admitted.

Lemma vec_mx_eq0 m n (v : 'rV_(m * n)) : (vec_mx v == 0) = (v == 0).
Proof.
Admitted.

Lemma row_mx0 m n1 n2 : row_mx 0 0 = 0 :> 'M_(m, n1 + n2).
Proof.
Admitted.

Lemma col_mx0 m1 m2 n : col_mx 0 0 = 0 :> 'M_(m1 + m2, n).
Proof.
Admitted.

Lemma block_mx0 m1 m2 n1 n2 : block_mx 0 0 0 0 = 0 :> 'M_(m1 + m2, n1 + n2).
Proof.
Admitted.

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

Lemma add_row_mx m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) B1 B2 :
  row_mx A1 A2 + row_mx B1 B2 = row_mx (A1 + B1) (A2 + B2).
Proof.
Admitted.

Lemma add_col_mx m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) B1 B2 :
  col_mx A1 A2 + col_mx B1 B2 = col_mx (A1 + B1) (A2 + B2).
Proof.
Admitted.

Lemma add_block_mx m1 m2 n1 n2 (Aul : 'M_(m1, n1)) Aur Adl (Adr : 'M_(m2, n2))
                   Bul Bur Bdl Bdr :
  let A := block_mx Aul Aur Adl Adr in let B := block_mx Bul Bur Bdl Bdr in
  A + B = block_mx (Aul + Bul) (Aur + Bur) (Adl + Bdl) (Adr + Bdr).
Proof.
Admitted.

Lemma row_mx_eq0 (m n1 n2 : nat) (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)):
  (row_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
Admitted.

Lemma col_mx_eq0 (m1 m2 n : nat) (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)):
  (col_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
Admitted.

Lemma block_mx_eq0 m1 m2 n1 n2 (Aul : 'M_(m1, n1)) Aur Adl (Adr : 'M_(m2, n2)) :
  (block_mx Aul Aur Adl Adr == 0) =
  [&& Aul == 0, Aur == 0, Adl == 0 & Adr == 0].
Proof.
Admitted.

Lemma trmx_eq0  m n (A : 'M_(m, n)) : (A^T == 0) = (A == 0).
Proof.
Admitted.

Lemma matrix_eq0 m n (A : 'M_(m, n)) :
  (A == 0) = [forall i, forall j, A i j == 0].
Proof.
Admitted.

Lemma matrix0Pn m n (A : 'M_(m, n)) : reflect (exists i j, A i j != 0) (A != 0).
Proof.
Admitted.

Lemma rV0Pn n (v : 'rV_n) : reflect (exists i, v 0 i != 0) (v != 0).
Proof.
Admitted.

Lemma cV0Pn n (v : 'cV_n) : reflect (exists i, v i 0 != 0) (v != 0).
Proof.
Admitted.

Definition nz_row m n (A : 'M_(m, n)) :=
  oapp (fun i => row i A) 0 [pick i | row i A != 0].

Lemma nz_row_eq0 m n (A : 'M_(m, n)) : (nz_row A == 0) = (A == 0).
Proof.
Admitted.

Definition is_diag_mx m n (A : 'M[V]_(m, n)) :=
  [forall i : 'I__, forall j : 'I__, (i != j :> nat) ==> (A i j == 0)].

Lemma is_diag_mxP m n (A : 'M[V]_(m, n)) :
  reflect (forall i j : 'I__, i != j :> nat -> A i j = 0) (is_diag_mx A).
Proof.
Admitted.

Lemma mx0_is_diag m n : is_diag_mx (0 : 'M[V]_(m, n)).
Proof.
Admitted.

Lemma mx11_is_diag (M : 'M_1) : is_diag_mx M.
Proof.
Admitted.

Definition is_trig_mx m n (A : 'M[V]_(m, n)) :=
  [forall i : 'I__, forall j : 'I__, (i < j)%N ==> (A i j == 0)].

Lemma is_trig_mxP m n (A : 'M[V]_(m, n)) :
  reflect (forall i j : 'I__, (i < j)%N -> A i j = 0) (is_trig_mx A).
Proof.
Admitted.

Lemma is_diag_mx_is_trig m n (A : 'M[V]_(m, n)) : is_diag_mx A -> is_trig_mx A.
Proof.
Admitted.

Lemma mx0_is_trig m n : is_trig_mx (0 : 'M[V]_(m, n)).
Proof.
Admitted.

Lemma mx11_is_trig (M : 'M_1) : is_trig_mx M.
Proof.
Admitted.

Lemma is_diag_mxEtrig m n (A : 'M[V]_(m, n)) :
  is_diag_mx A = is_trig_mx A && is_trig_mx A^T.
Proof.
Admitted.

Lemma is_diag_trmx  m n (A : 'M[V]_(m, n)) : is_diag_mx A^T = is_diag_mx A.
Proof.
Admitted.

Lemma ursubmx_trig m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  m1 <= n1 -> is_trig_mx A -> ursubmx A = 0.
Proof.
Admitted.

Lemma dlsubmx_diag m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  n1 <= m1 -> is_diag_mx A -> dlsubmx A = 0.
Proof.
Admitted.

Lemma ulsubmx_trig m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  is_trig_mx A -> is_trig_mx (ulsubmx A).
Proof.
Admitted.

Lemma drsubmx_trig m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  m1 <= n1 -> is_trig_mx A -> is_trig_mx (drsubmx A).
Proof.
Admitted.

Lemma ulsubmx_diag m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  is_diag_mx A -> is_diag_mx (ulsubmx A).
Proof.
Admitted.

Lemma drsubmx_diag m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  m1 = n1 -> is_diag_mx A -> is_diag_mx (drsubmx A).
Proof.
Admitted.

Lemma is_trig_block_mx m1 m2 n1 n2 ul ur dl dr : m1 = n1 ->
  @is_trig_mx (m1 + m2) (n1 + n2) (block_mx ul ur dl dr) =
  [&& ur == 0, is_trig_mx ul & is_trig_mx dr].
Proof.
Admitted.

Lemma trigmx_ind (P : forall m n, 'M_(m, n) -> Type) :
  (forall m, P m 0 0) ->
  (forall n, P 0 n 0) ->
  (forall m n x c A, is_trig_mx A ->
    P m n A -> P (1 + m)%N (1 + n)%N (block_mx x 0 c A)) ->
  forall m n A, is_trig_mx A -> P m n A.
Proof.
Admitted.

Lemma trigsqmx_ind (P : forall n, 'M[V]_n -> Type) : (P 0 0) ->
  (forall n x c A, is_trig_mx A -> P n A -> P (1 + n)%N (block_mx x 0 c A)) ->
  forall n A, is_trig_mx A -> P n A.
Proof.
Admitted.

Lemma is_diag_block_mx m1 m2 n1 n2 ul ur dl dr : m1 = n1 ->
  @is_diag_mx (m1 + m2) (n1 + n2) (block_mx ul ur dl dr) =
  [&& ur == 0, dl == 0, is_diag_mx ul & is_diag_mx dr].
Proof.
Admitted.

Lemma diagmx_ind (P : forall m n, 'M_(m, n) -> Type) :
  (forall m, P m 0 0) ->
  (forall n, P 0 n 0) ->
  (forall m n x c A, is_diag_mx A ->
    P m n A -> P (1 + m)%N (1 + n)%N (block_mx x 0 c A)) ->
  forall m n A, is_diag_mx A -> P m n A.
Proof.
Admitted.

Lemma diagsqmx_ind (P : forall n, 'M[V]_n -> Type) :
    (P 0 0) ->
  (forall n x c A, is_diag_mx A -> P n A -> P (1 + n)%N (block_mx x 0 c A)) ->
  forall n A, is_diag_mx A -> P n A.
Proof.
Admitted.

(* Diagonal matrices *)

Fact diag_mx_key : unit.
Proof.
Admitted.
Definition diag_mx n (d : 'rV[V]_n) :=
  \matrix[diag_mx_key]_(i, j) (d 0 i *+ (i == j)).

Lemma tr_diag_mx n (d : 'rV_n) : (diag_mx d)^T = diag_mx d.
Proof.
Admitted.

Fact diag_mx_is_nmod_morphism n : nmod_morphism (@diag_mx n).
Proof.
Admitted.
#[deprecated(since="mathcomp 2.5.0", use=diag_mx_is_nmod_morphism)]
Definition diag_mx_is_semi_additive := diag_mx_is_nmod_morphism.
HB.instance Definition _ n := GRing.isNmodMorphism.Build 'rV_n 'M_n (@diag_mx n)
  (@diag_mx_is_nmod_morphism n).

Lemma diag_mx_row m n (l : 'rV_n) (r : 'rV_m) :
  diag_mx (row_mx l r) = block_mx (diag_mx l) 0 0 (diag_mx r).
Proof.
Admitted.

Lemma diag_mxP n (A : 'M[V]_n) :
  reflect (exists d : 'rV_n, A = diag_mx d) (is_diag_mx A).
Proof.
Admitted.

Lemma diag_mx_is_diag n (r : 'rV[V]_n) : is_diag_mx (diag_mx r).
Proof.
Admitted.

Lemma diag_mx_is_trig n (r : 'rV[V]_n) : is_trig_mx (diag_mx r).
Proof.
Admitted.

(* Scalar matrix : a diagonal matrix with a constant on the diagonal *)
Section ScalarMx.

Variable n : nat.

Fact scalar_mx_key : unit.
Proof.
Admitted.
Definition scalar_mx x : 'M[V]_n :=
  \matrix[scalar_mx_key]_(i , j) (x *+ (i == j)).
Notation "x %:M" := (scalar_mx x) : ring_scope.

Lemma diag_const_mx a : diag_mx (const_mx a) = a%:M :> 'M_n.
Proof.
Admitted.

Lemma tr_scalar_mx a : (a%:M)^T = a%:M.
Proof.
Admitted.

Fact scalar_mx_is_nmod_morphism : nmod_morphism scalar_mx.
Proof.
Admitted.
#[deprecated(since="mathcomp 2.5.0", use=scalar_mx_is_nmod_morphism)]
Definition scalar_mx_is_semi_additive := scalar_mx_is_nmod_morphism.
HB.instance Definition _ := GRing.isNmodMorphism.Build V 'M_n scalar_mx
  scalar_mx_is_nmod_morphism.

Definition is_scalar_mx (A : 'M[V]_n) :=
  if insub 0 is Some i then A == (A i i)%:M else true.

Lemma is_scalar_mxP A : reflect (exists a, A = a%:M) (is_scalar_mx A).
Proof.
Admitted.

Lemma scalar_mx_is_scalar a : is_scalar_mx a%:M.
Proof.
Admitted.

Lemma mx0_is_scalar : is_scalar_mx 0.
Proof.
Admitted.

Lemma scalar_mx_is_diag a : is_diag_mx a%:M.
Proof.
Admitted.

Lemma is_scalar_mx_is_diag A : is_scalar_mx A -> is_diag_mx A.
Proof.
Admitted.

Lemma scalar_mx_is_trig a : is_trig_mx a%:M.
Proof.
Admitted.

Lemma is_scalar_mx_is_trig A : is_scalar_mx A -> is_trig_mx A.
Proof.
Admitted.

End ScalarMx.

Notation "x %:M" := (scalar_mx _ x) : ring_scope.

Lemma mx11_scalar (A : 'M_1) : A = (A 0 0)%:M.
Proof.
Admitted.

Lemma scalar_mx_block n1 n2 a : a%:M = block_mx a%:M 0 0 a%:M :> 'M_(n1 + n2).
Proof.
Admitted.

(* The trace. *)
Section Trace.

Variable n : nat.
(*TODO: undergeneralize to monoid *)
Definition mxtrace (A : 'M[V]_n) := \sum_i A i i.
Local Notation "'\tr' A" := (mxtrace A) : ring_scope.

Lemma mxtrace_tr A : \tr A^T = \tr A.
Proof.
Admitted.

Fact mxtrace_is_nmod_morphism : nmod_morphism mxtrace.
Proof.
Admitted.
#[deprecated(since="mathcomp 2.5.0", use=mxtrace_is_nmod_morphism)]
Definition mxtrace_is_semi_additive := mxtrace_is_nmod_morphism.
HB.instance Definition _ := GRing.isNmodMorphism.Build 'M_n V mxtrace
  mxtrace_is_nmod_morphism.

Lemma mxtrace0 : \tr 0 = 0.
Proof.
Admitted.
Lemma mxtraceD A B : \tr (A + B) = \tr A + \tr B.
Proof.
Admitted.

Lemma mxtrace_diag D : \tr (diag_mx D) = \sum_j D 0 j.
Proof.
Admitted.

Lemma mxtrace_scalar a : \tr a%:M = a *+ n.
Proof.
Admitted.

End Trace.
Local Notation "'\tr' A" := (mxtrace A) : ring_scope.

Lemma trace_mx11 (A : 'M_1) : \tr A = A 0 0.
Proof.
Admitted.

Lemma mxtrace_block n1 n2 (Aul : 'M_n1) Aur Adl (Adr : 'M_n2) :
  \tr (block_mx Aul Aur Adl Adr) = \tr Aul + \tr Adr.
Proof.
Admitted.

End MatrixNmodule.

Arguments is_diag_mx {V m n}.
Arguments is_diag_mxP {V m n A}.
Arguments is_trig_mx {V m n}.
Arguments is_trig_mxP {V m n A}.
Arguments scalar_mx {V n}.
Arguments is_scalar_mxP {V n A}.

Notation "\tr A" := (mxtrace A) : ring_scope.

(* Parametricity over the semi-additive structure. *)
Section MapNmodMatrix.

Variables (aR rR : nmodType) (f : {additive aR -> rR}) (m n : nat).
Local Notation "A ^f" := (map_mx f A) : ring_scope.
Implicit Type A : 'M[aR]_(m, n).

Lemma map_mx0 : 0^f = 0 :> 'M_(m, n).
Proof.
Admitted.

Lemma map_mxD A B : (A + B)^f = A^f + B^f.
Proof.
Admitted.

Definition map_mx_sum := big_morph _ map_mxD map_mx0.

HB.instance Definition _ :=
  GRing.isNmodMorphism.Build 'M[aR]_(m, n) 'M[rR]_(m, n) (map_mx f)
    (map_mx0, map_mxD).

End MapNmodMatrix.

Section MatrixZmodule.

Variable V : zmodType.

Section FixedDim.

Variables m n : nat.
Implicit Types A B : 'M[V]_(m, n).

Fact oppmx_key : unit.
Proof.
Admitted.
Definition oppmx := @map_mx V V -%R m n.

Lemma addNmx : left_inverse (const_mx 0) oppmx (@addmx V m n).
Proof.
Admitted.

HB.instance Definition _ := GRing.Nmodule_isZmodule.Build 'M[V]_(m, n) addNmx.

#[deprecated(since="mathcomp 2.5.0", use=raddfB)]
Fact const_mx_is_zmod_morphism : zmod_morphism const_mx.
Proof.
Admitted.
#[deprecated(since="mathcomp 2.5.0", use=raddfB),
  warning="-deprecated"]
Definition const_mx_is_additive := const_mx_is_zmod_morphism.

End FixedDim.

Section Additive.

Variables (m n p q : nat) (f : 'I_p -> 'I_q -> 'I_m) (g : 'I_p -> 'I_q -> 'I_n).

#[deprecated(since="mathcomp 2.5.0", use=raddfB)]
Fact swizzle_mx_is_zmod_morphism k : zmod_morphism (swizzle_mx f g k).
Proof.
Admitted.
#[deprecated(since="mathcomp 2.5.0", use=raddfB),
  warning="-deprecated"]
Definition swizzle_mx_is_additive := swizzle_mx_is_zmod_morphism.

End Additive.

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

Lemma opp_row_mx m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  - row_mx A1 A2 = row_mx (- A1) (- A2).
Proof.
Admitted.

Lemma opp_col_mx m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  - col_mx A1 A2 = col_mx (- A1) (- A2).
Proof.
Admitted.

Lemma opp_block_mx m1 m2 n1 n2 (Aul : 'M_(m1, n1)) Aur Adl (Adr : 'M_(m2, n2)) :
  - block_mx Aul Aur Adl Adr = block_mx (- Aul) (- Aur) (- Adl) (- Adr).
Proof.
Admitted.

(* Diagonal matrices *)

#[deprecated(since="mathcomp 2.5.0", use=raddfB)]
Fact diag_mx_is_zmod_morphism n : zmod_morphism (@diag_mx V n).
Proof.
Admitted.
#[deprecated(since="mathcomp 2.5.0", use=raddfB),
  warning="-deprecated"]
Definition diag_mx_is_additive := diag_mx_is_zmod_morphism.

(* Scalar matrix : a diagonal matrix with a constant on the diagonal *)
Section ScalarMx.

Variable n : nat.

#[deprecated(since="mathcomp 2.5.0", use=raddfB)]
Fact scalar_mx_is_zmod_morphism : zmod_morphism (@scalar_mx V n).
Proof.
Admitted.
#[deprecated(since="mathcomp 2.5.0", use=raddfB),
  warning="-deprecated"]
Definition scalar_mx_is_additive := scalar_mx_is_zmod_morphism.

End ScalarMx.

(* The trace. *)
Section Trace.

Variable n : nat.

#[deprecated(since="mathcomp 2.5.0", use=raddfB)]
Fact mxtrace_is_zmod_morphism : zmod_morphism (@mxtrace V n).
Proof.
Admitted.
#[deprecated(since="mathcomp 2.5.0", use=raddfB),
  warning="-deprecated"]
Definition mxtrace_is_additive := mxtrace_is_zmod_morphism.

End Trace.

End MatrixZmodule.

(* Parametricity over the additive structure. *)
Section MapZmodMatrix.

Variables (aR rR : zmodType) (f : {additive aR -> rR}) (m n : nat).
Local Notation "A ^f" := (map_mx f A) : ring_scope.
Implicit Type A : 'M[aR]_(m, n).

Lemma map_mxN A : (- A)^f = - A^f.
Proof.
Admitted.

Lemma map_mxB A B : (A - B)^f = A^f - B^f.
Proof.
Admitted.

End MapZmodMatrix.

(*****************************************************************************)
(*********** Matrix ring module, graded ring, and ring structures ************)
(*****************************************************************************)

Section MatrixAlgebra.

Variable R : pzSemiRingType.

Section SemiRingModule.

(* The ring module/vector space structure *)

Variables m n : nat.
Implicit Types A B : 'M[R]_(m, n).

Fact scalemx_key : unit.
Proof.
Admitted.
Definition scalemx x A := \matrix[scalemx_key]_(i, j) (x * A i j).

(* Basis *)
Fact delta_mx_key : unit.
Proof.
Admitted.
Definition delta_mx i0 j0 : 'M[R]_(m, n) :=
  \matrix[delta_mx_key]_(i, j) ((i == i0) && (j == j0))%:R.

Local Notation "x *m: A" := (scalemx x A) (at level 40) : ring_scope.

Fact scale0mx A : 0 *m: A = 0.
Proof.
Admitted.

Fact scale1mx A : 1 *m: A = A.
Proof.
Admitted.

Fact scalemxDl A x y : (x + y) *m: A = x *m: A + y *m: A.
Proof.
Admitted.

Fact scalemxDr x A B : x *m: (A + B) = x *m: A + x *m: B.
Proof.
Admitted.

Fact scalemxA x y A : x *m: (y *m: A) = (x * y) *m: A.
Proof.
Admitted.

HB.instance Definition _ :=
  GRing.Nmodule_isLSemiModule.Build R 'M[R]_(m, n)
  scalemxA scale0mx scale1mx scalemxDr scalemxDl.

Lemma scalemx_const a b : a *: const_mx b = const_mx (a * b).
Proof.
Admitted.

Lemma matrix_sum_delta A : A = \sum_(i < m) \sum_(j < n) A i j *: delta_mx i j.
Proof.
Admitted.

End SemiRingModule.

Lemma trmx_delta m n i j : (delta_mx i j)^T = delta_mx j i :> 'M[R]_(n, m).
Proof.
Admitted.

Lemma delta_mx_lshift m n1 n2 i j :
  delta_mx i (lshift n2 j) = row_mx (delta_mx i j) 0 :> 'M_(m, n1 + n2).
Proof.
Admitted.

Lemma delta_mx_rshift m n1 n2 i j :
  delta_mx i (rshift n1 j) = row_mx 0 (delta_mx i j) :> 'M_(m, n1 + n2).
Proof.
Admitted.

Lemma delta_mx_ushift m1 m2 n i j :
  delta_mx (lshift m2 i) j = col_mx (delta_mx i j) 0 :> 'M_(m1 + m2, n).
Proof.
Admitted.

Lemma delta_mx_dshift m1 m2 n i j :
  delta_mx (rshift m1 i) j = col_mx 0 (delta_mx i j) :> 'M_(m1 + m2, n).
Proof.
Admitted.

Lemma vec_mx_delta m n i j :
  vec_mx (delta_mx 0 (mxvec_index i j)) = delta_mx i j :> 'M_(m, n).
Proof.
Admitted.

Lemma mxvec_delta m n i j :
  mxvec (delta_mx i j) = delta_mx 0 (mxvec_index i j) :> 'rV_(m * n).
Proof.
Admitted.

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

(* Scalar matrix *)

Notation "x %:M" := (scalar_mx x) : ring_scope.

Lemma trmx1 n : (1%:M)^T = 1%:M :> 'M[R]_n.
Proof.
Admitted.

Lemma row1 n i : row i (1%:M : 'M_n) = delta_mx 0 i.
Proof.
Admitted.

Lemma col1 n i : col i (1%:M : 'M_n) = delta_mx i 0.
Proof.
Admitted.

(* Matrix multiplication using bigops. *)
Fact mulmx_key : unit.
Proof.
Admitted.
Definition mulmx {m n p} (A : 'M_(m, n)) (B : 'M_(n, p)) : 'M[R]_(m, p) :=
  \matrix[mulmx_key]_(i, k) \sum_j (A i j * B j k).

Local Notation "A *m B" := (mulmx A B) : ring_scope.

Lemma mulmxA m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)) :
  A *m (B *m C) = A *m B *m C.
Proof.
Admitted.

Lemma mul0mx m n p (A : 'M_(n, p)) : 0 *m A = 0 :> 'M_(m, p).
Proof.
Admitted.

Lemma mulmx0 m n p (A : 'M_(m, n)) : A *m 0 = 0 :> 'M_(m, p).
Proof.
Admitted.

Lemma mulmxDl m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)) :
  (A1 + A2) *m B = A1 *m B + A2 *m B.
Proof.
Admitted.

Lemma mulmxDr m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *m (B1 + B2) = A *m B1 + A *m B2.
Proof.
Admitted.

HB.instance Definition _ m n p A :=
  GRing.isNmodMorphism.Build 'M_(n, p) 'M_(m, p) (mulmx A)
    (mulmx0 _ A, mulmxDr A).

Lemma scalemxAl m n p a (A : 'M_(m, n)) (B : 'M_(n, p)) :
  a *: (A *m B) = (a *: A) *m B.
Proof.
Admitted.

Lemma mulmx_suml m n p (A : 'M_(n, p)) I r P (B_ : I -> 'M_(m, n)) :
  (\sum_(i <- r | P i) B_ i) *m A = \sum_(i <- r | P i) B_ i *m A.
Proof.
Admitted.

Lemma mulmx_sumr m n p (A : 'M_(m, n)) I r P (B_ : I -> 'M_(n, p)) :
  A *m (\sum_(i <- r | P i) B_ i) = \sum_(i <- r | P i) A *m B_ i.
Proof.
Admitted.

Lemma rowE m n i (A : 'M_(m, n)) : row i A = delta_mx 0 i *m A.
Proof.
Admitted.

Lemma colE m n i (A : 'M_(m, n)) : col i A = A *m delta_mx i 0.
Proof.
Admitted.

Lemma mul_rVP m n A B : ((@mulmx 1 m n)^~ A =1 mulmx^~ B) <-> (A = B).
Proof.
Admitted.

Lemma row_mul m n p (i : 'I_m) A (B : 'M_(n, p)) :
  row i (A *m B) = row i A *m B.
Proof.
Admitted.

Lemma mxsub_mul m n m' n' p f g (A : 'M_(m, p)) (B : 'M_(p, n)) :
  mxsub f g (A *m B) = rowsub f A *m colsub g B :> 'M_(m', n').
Proof.
Admitted.

Lemma mul_rowsub_mx m n m' p f (A : 'M_(m, p)) (B : 'M_(p, n)) :
  rowsub f A *m B = rowsub f (A *m B) :> 'M_(m', n).
Proof.
Admitted.

Lemma mulmx_colsub m n n' p g (A : 'M_(m, p)) (B : 'M_(p, n)) :
  A *m colsub g B = colsub g (A *m B) :> 'M_(m, n').
Proof.
Admitted.

Lemma mul_delta_mx_cond m n p (j1 j2 : 'I_n) (i1 : 'I_m) (k2 : 'I_p) :
  delta_mx i1 j1 *m delta_mx j2 k2 = delta_mx i1 k2 *+ (j1 == j2).
Proof.
Admitted.

Lemma mul_delta_mx m n p (j : 'I_n) (i : 'I_m) (k : 'I_p) :
  delta_mx i j *m delta_mx j k = delta_mx i k.
Proof.
Admitted.

Lemma mul_delta_mx_0 m n p (j1 j2 : 'I_n) (i1 : 'I_m) (k2 : 'I_p) :
  j1 != j2 -> delta_mx i1 j1 *m delta_mx j2 k2 = 0.
Proof.
Admitted.

Lemma mul_diag_mx m n d (A : 'M_(m, n)) :
  diag_mx d *m A = \matrix_(i, j) (d 0 i * A i j).
Proof.
Admitted.

Lemma mul_mx_diag m n (A : 'M_(m, n)) d :
  A *m diag_mx d = \matrix_(i, j) (A i j * d 0 j).
Proof.
Admitted.

Lemma mulmx_diag n (d e : 'rV_n) :
  diag_mx d *m diag_mx e = diag_mx (\row_j (d 0 j * e 0 j)).
Proof.
Admitted.

Lemma scalar_mxM n a b : (a * b)%:M = a%:M *m b%:M :> 'M_n.
Proof.
Admitted.

Lemma mul1mx m n (A : 'M_(m, n)) : 1%:M *m A = A.
Proof.
Admitted.

Lemma mulmx1 m n (A : 'M_(m, n)) : A *m 1%:M = A.
Proof.
Admitted.

Lemma rowsubE m m' n f (A : 'M_(m, n)) :
  rowsub f A = rowsub f 1%:M *m A :> 'M_(m', n).
Proof.
Admitted.

(* mulmx and col_perm, row_perm, xcol, xrow *)

Lemma mul_col_perm m n p s (A : 'M_(m, n)) (B : 'M_(n, p)) :
  col_perm s A *m B = A *m row_perm s^-1 B.
Proof.
Admitted.

Lemma mul_row_perm m n p s (A : 'M_(m, n)) (B : 'M_(n, p)) :
  A *m row_perm s B = col_perm s^-1 A *m B.
Proof.
Admitted.

Lemma mul_xcol m n p j1 j2 (A : 'M_(m, n)) (B : 'M_(n, p)) :
  xcol j1 j2 A *m B = A *m xrow j1 j2 B.
Proof.
Admitted.

(* Permutation matrix *)

Definition perm_mx n s : 'M_n := row_perm s (1%:M : 'M[R]_n).

Definition tperm_mx n i1 i2 : 'M_n := perm_mx (tperm i1 i2).

Lemma col_permE m n s (A : 'M_(m, n)) : col_perm s A = A *m perm_mx s^-1.
Proof.
Admitted.

Lemma row_permE m n s (A : 'M_(m, n)) : row_perm s A = perm_mx s *m A.
Proof.
Admitted.

Lemma xcolE m n j1 j2 (A : 'M_(m, n)) : xcol j1 j2 A = A *m tperm_mx j1 j2.
Proof.
Admitted.

Lemma xrowE m n i1 i2 (A : 'M_(m, n)) : xrow i1 i2 A = tperm_mx i1 i2 *m A.
Proof.
Admitted.

Lemma perm_mxEsub n s : @perm_mx n s = rowsub s 1%:M.
Proof.
Admitted.

Lemma tperm_mxEsub n i1 i2 : @tperm_mx n i1 i2 = rowsub (tperm i1 i2) 1%:M.
Proof.
Admitted.

Lemma tr_perm_mx n (s : 'S_n) : (perm_mx s)^T = perm_mx s^-1.
Proof.
Admitted.

Lemma tr_tperm_mx n i1 i2 : (tperm_mx i1 i2)^T = tperm_mx i1 i2 :> 'M_n.
Proof.
Admitted.

Lemma perm_mx1 n : perm_mx 1 = 1%:M :> 'M_n.
Proof.
Admitted.

Lemma perm_mxM n (s t : 'S_n) : perm_mx (s * t) = perm_mx s *m perm_mx t.
Proof.
Admitted.

Definition is_perm_mx n (A : 'M_n) := [exists s, A == perm_mx s].

Lemma is_perm_mxP n (A : 'M_n) :
  reflect (exists s, A = perm_mx s) (is_perm_mx A).
Proof.
Admitted.

Lemma perm_mx_is_perm n (s : 'S_n) : is_perm_mx (perm_mx s).
Proof.
Admitted.

Lemma is_perm_mx1 n : is_perm_mx (1%:M : 'M_n).
Proof.
Admitted.

Lemma is_perm_mxMl n (A B : 'M_n) :
  is_perm_mx A -> is_perm_mx (A *m B) = is_perm_mx B.
Proof.
Admitted.

Lemma is_perm_mx_tr n (A : 'M_n) : is_perm_mx A^T = is_perm_mx A.
Proof.
Admitted.

Lemma is_perm_mxMr n (A B : 'M_n) :
  is_perm_mx B -> is_perm_mx (A *m B) = is_perm_mx A.
Proof.
Admitted.

(* Partial identity matrix (used in rank decomposition). *)

Fact pid_mx_key : unit.
Proof.
Admitted.
Definition pid_mx {m n} r : 'M[R]_(m, n) :=
  \matrix[pid_mx_key]_(i, j) ((i == j :> nat) && (i < r))%:R.

Lemma pid_mx_0 m n : pid_mx 0 = 0 :> 'M_(m, n).
Proof.
Admitted.

Lemma pid_mx_1 r : pid_mx r = 1%:M :> 'M_r.
Proof.
Admitted.

Lemma pid_mx_row n r : pid_mx r = row_mx 1%:M 0 :> 'M_(r, r + n).
Proof.
Admitted.

Lemma pid_mx_col m r : pid_mx r = col_mx 1%:M 0 :> 'M_(r + m, r).
Proof.
Admitted.

Lemma pid_mx_block m n r : pid_mx r = block_mx 1%:M 0 0 0 :> 'M_(r + m, r + n).
Proof.
Admitted.

Lemma tr_pid_mx m n r : (pid_mx r)^T = pid_mx r :> 'M_(n, m).
Proof.
Admitted.

Lemma pid_mx_minv m n r : pid_mx (minn m r) = pid_mx r :> 'M_(m, n).
Proof.
Admitted.

Lemma pid_mx_minh m n r : pid_mx (minn n r) = pid_mx r :> 'M_(m, n).
Proof.
Admitted.

Lemma mul_pid_mx m n p q r :
  (pid_mx q : 'M_(m, n)) *m (pid_mx r : 'M_(n, p)) = pid_mx (minn n (minn q r)).
Proof.
Admitted.

Lemma pid_mx_id m n p r :
  r <= n -> (pid_mx r : 'M_(m, n)) *m (pid_mx r : 'M_(n, p)) = pid_mx r.
Proof.
Admitted.

Lemma pid_mxErow m n (le_mn : m <= n) :
  pid_mx m = rowsub (widen_ord le_mn) 1%:M.
Proof.
Admitted.

Lemma pid_mxEcol m n (le_mn : m <= n) :
  pid_mx n = colsub (widen_ord le_mn) 1%:M.
Proof.
Admitted.

(* Block products; we cover all 1 x 2, 2 x 1, and 2 x 2 block products. *)
Lemma mul_mx_row m n p1 p2 (A : 'M_(m, n)) (Bl : 'M_(n, p1)) (Br : 'M_(n, p2)) :
  A *m row_mx Bl Br = row_mx (A *m Bl) (A *m Br).
Proof.
Admitted.

Lemma mul_col_mx m1 m2 n p (Au : 'M_(m1, n)) (Ad : 'M_(m2, n)) (B : 'M_(n, p)) :
  col_mx Au Ad *m B = col_mx (Au *m B) (Ad *m B).
Proof.
Admitted.

Lemma mul_row_col m n1 n2 p (Al : 'M_(m, n1)) (Ar : 'M_(m, n2))
                            (Bu : 'M_(n1, p)) (Bd : 'M_(n2, p)) :
  row_mx Al Ar *m col_mx Bu Bd = Al *m Bu + Ar *m Bd.
Proof.
Admitted.

Lemma mul_col_row m1 m2 n p1 p2 (Au : 'M_(m1, n)) (Ad : 'M_(m2, n))
                                (Bl : 'M_(n, p1)) (Br : 'M_(n, p2)) :
  col_mx Au Ad *m row_mx Bl Br
     = block_mx (Au *m Bl) (Au *m Br) (Ad *m Bl) (Ad *m Br).
Proof.
Admitted.

Lemma mul_row_block m n1 n2 p1 p2 (Al : 'M_(m, n1)) (Ar : 'M_(m, n2))
                                  (Bul : 'M_(n1, p1)) (Bur : 'M_(n1, p2))
                                  (Bdl : 'M_(n2, p1)) (Bdr : 'M_(n2, p2)) :
  row_mx Al Ar *m block_mx Bul Bur Bdl Bdr
   = row_mx (Al *m Bul + Ar *m Bdl) (Al *m Bur + Ar *m Bdr).
Proof.
Admitted.

Lemma mul_block_col m1 m2 n1 n2 p (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2))
                                  (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2))
                                  (Bu : 'M_(n1, p)) (Bd : 'M_(n2, p)) :
  block_mx Aul Aur Adl Adr *m col_mx Bu Bd
   = col_mx (Aul *m Bu + Aur *m Bd) (Adl *m Bu + Adr *m Bd).
Proof.
Admitted.

Lemma mulmx_block m1 m2 n1 n2 p1 p2 (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2))
                                    (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2))
                                    (Bul : 'M_(n1, p1)) (Bur : 'M_(n1, p2))
                                    (Bdl : 'M_(n2, p1)) (Bdr : 'M_(n2, p2)) :
  block_mx Aul Aur Adl Adr *m block_mx Bul Bur Bdl Bdr
    = block_mx (Aul *m Bul + Aur *m Bdl) (Aul *m Bur + Aur *m Bdr)
               (Adl *m Bul + Adr *m Bdl) (Adl *m Bur + Adr *m Bdr).
Proof.
Admitted.

Lemma mulmx_lsub m n p k (A : 'M_(m, n)) (B : 'M_(n, p + k)) :
  A *m lsubmx B = lsubmx (A *m B).
Proof.
Admitted.

Lemma mulmx_rsub m n p k (A : 'M_(m, n)) (B : 'M_(n, p + k)) :
  A *m rsubmx B = rsubmx (A *m B).
Proof.
Admitted.

Lemma mul_usub_mx m k n p (A : 'M_(m + k, n)) (B : 'M_(n, p)) :
  usubmx A *m B = usubmx (A *m B).
Proof.
Admitted.

Lemma mul_dsub_mx m k n p (A : 'M_(m + k, n)) (B : 'M_(n, p)) :
  dsubmx A *m B = dsubmx (A *m B).
Proof.
Admitted.

(* The trace *)

Section Trace.
Variable n : nat.

Lemma mxtrace1 : \tr (1%:M : 'M[R]_n) = n%:R.
Proof.
Admitted.

Lemma mxtraceZ a (A : 'M_n) : \tr (a *: A) = a * \tr A.
Proof.
Admitted.

HB.instance Definition _ :=
  GRing.isScalable.Build R 'M_n R _ (@mxtrace _ n) mxtraceZ.

End Trace.

Section StructuralLinear.

Fact swizzle_mx_is_scalable m n p q f g k :
  scalable (@swizzle_mx R m n p q f g k).
Proof.
Admitted.
HB.instance Definition _ m n p q f g k :=
  GRing.isScalable.Build R 'M[R]_(m, n) 'M[R]_(p, q) *:%R (swizzle_mx f g k)
    (swizzle_mx_is_scalable f g k).

Local Notation SwizzleLin op := (GRing.Linear.copy op (swizzle_mx _ _ _)).

HB.instance Definition _ m n := SwizzleLin (@trmx R m n).
HB.instance Definition _ m n i := SwizzleLin (@row R m n i).
HB.instance Definition _ m n j := SwizzleLin (@col R m n j).
HB.instance Definition _ m n i := SwizzleLin (@row' R m n i).
HB.instance Definition _ m n j := SwizzleLin (@col' R m n j).
HB.instance Definition _ m n m' n' f g := SwizzleLin (@mxsub R m n m' n' f g).
HB.instance Definition _ m n s := SwizzleLin (@row_perm R m n s).
HB.instance Definition _ m n s := SwizzleLin (@col_perm R m n s).
HB.instance Definition _ m n i1 i2 := SwizzleLin (@xrow R m n i1 i2).
HB.instance Definition _ m n j1 j2 := SwizzleLin (@xcol R m n j1 j2).
HB.instance Definition _ m n1 n2 := SwizzleLin (@lsubmx R m n1 n2).
HB.instance Definition _ m n1 n2 := SwizzleLin (@rsubmx R m n1 n2).
HB.instance Definition _ m1 m2 n := SwizzleLin (@usubmx R m1 m2 n).
HB.instance Definition _ m1 m2 n := SwizzleLin (@dsubmx R m1 m2 n).

HB.instance Definition _ m n := SwizzleLin (@vec_mx R m n).
Definition mxvec_is_scalable m n := can2_scalable (@vec_mxK R m n) mxvecK.
HB.instance Definition _ m n :=
  GRing.isScalable.Build R 'M_(m, n) 'rV_(m * n) *:%R mxvec
    (@mxvec_is_scalable m n).

End StructuralLinear.

Lemma row_sum_delta n (u : 'rV_n) : u = \sum_(j < n) u 0 j *: delta_mx 0 j.
Proof.
Admitted.

Lemma scale_row_mx m n1 n2 a (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  a *: row_mx A1 A2 = row_mx (a *: A1) (a *: A2).
Proof.
Admitted.

Lemma scale_col_mx m1 m2 n a (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  a *: col_mx A1 A2 = col_mx (a *: A1) (a *: A2).
Proof.
Admitted.

Lemma scale_block_mx m1 m2 n1 n2 a (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2))
                                   (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2)) :
  a *: block_mx Aul Aur Adl Adr
     = block_mx (a *: Aul) (a *: Aur) (a *: Adl) (a *: Adr).
Proof.
Admitted.

(* Diagonal matrices *)

Fact diag_mx_is_scalable n : scalable (@diag_mx R n).
Proof.
Admitted.
HB.instance Definition _ n :=
  GRing.isScalable.Build R 'rV_n 'M_n _ (@diag_mx _ n) (@diag_mx_is_scalable n).

Lemma diag_mx_sum_delta n (d : 'rV_n) :
  diag_mx d = \sum_i d 0 i *: delta_mx i i.
Proof.
Admitted.

Lemma row_diag_mx n (d : 'rV_n) i : row i (diag_mx d) = d 0 i *: delta_mx 0 i.
Proof.
Admitted.

(* Scalar matrix *)

Lemma scale_scalar_mx n a1 a2 : a1 *: a2%:M = (a1 * a2)%:M :> 'M_n.
Proof.
Admitted.

Lemma scalemx1 n a : a *: 1%:M = a%:M :> 'M_n.
Proof.
Admitted.

Lemma scalar_mx_sum_delta n a : a%:M = \sum_i a *: delta_mx i i :> 'M_n.
Proof.
Admitted.

Lemma mx1_sum_delta n : 1%:M = \sum_i delta_mx i i :> 'M[R]_n.
Proof.
Admitted.

(* Right scaling associativity requires a commutative ring *)

Lemma mulmx_sum_row m n (u : 'rV_m) (A : 'M_(m, n)) :
  u *m A = \sum_i u 0 i *: row i A.
Proof.
Admitted.

Lemma mul_scalar_mx m n a (A : 'M_(m, n)) : a%:M *m A = a *: A.
Proof.
Admitted.

Section MatrixSemiRing.

Variable n : nat.

HB.instance Definition _ := GRing.Nmodule_isPzSemiRing.Build 'M[R]_n
  (@mulmxA n n n n) (@mul1mx n n) (@mulmx1 n n)
  (@mulmxDl n n n) (@mulmxDr n n n) (@mul0mx n n n) (@mulmx0 n n n).

HB.instance Definition _ :=
  GRing.LSemiModule_isLSemiAlgebra.Build R 'M[R]_n (@scalemxAl n n n).

Lemma mulmxE : mulmx = *%R.
Proof.
Admitted.
Lemma idmxE : 1%:M = 1 :> 'M_n.
Proof.
Admitted.

Fact scalar_mx_is_monoid_morphism : monoid_morphism (@scalar_mx R n).
Proof.
Admitted.
#[deprecated(since="mathcomp 2.5.0", use=scalar_mx_is_monoid_morphism)]
Definition scalar_mx_is_multiplicative := scalar_mx_is_monoid_morphism.
HB.instance Definition _ := GRing.isMonoidMorphism.Build R 'M_n (@scalar_mx _ n)
  scalar_mx_is_monoid_morphism.

End MatrixSemiRing.

(* Correspondence between matrices and linear function on row vectors. *)
Section LinRowVector.

Variables m n : nat.

Fact lin1_mx_key : unit.
Proof.
Admitted.
Definition lin1_mx (f : 'rV[R]_m -> 'rV[R]_n) :=
  \matrix[lin1_mx_key]_(i, j) f (delta_mx 0 i) 0 j.

Variable f : {linear 'rV[R]_m -> 'rV[R]_n}.

Lemma mul_rV_lin1 u : u *m lin1_mx f = f u.
Proof.
Admitted.

End LinRowVector.

(* Correspondence between matrices and linear function on matrices. *)
Section LinMatrix.

Variables m1 n1 m2 n2 : nat.

Definition lin_mx (f : 'M[R]_(m1, n1) -> 'M[R]_(m2, n2)) :=
  lin1_mx (mxvec \o f \o vec_mx).

Variable f : {linear 'M[R]_(m1, n1) -> 'M[R]_(m2, n2)}.

Lemma mul_rV_lin u : u *m lin_mx f = mxvec (f (vec_mx u)).
Proof.
Admitted.

Lemma mul_vec_lin A : mxvec A *m lin_mx f = mxvec (f A).
Proof.
Admitted.

Lemma mx_rV_lin u : vec_mx (u *m lin_mx f) = f (vec_mx u).
Proof.
Admitted.

Lemma mx_vec_lin A : vec_mx (mxvec A *m lin_mx f) = f A.
Proof.
Admitted.

End LinMatrix.

Section Mulmxr.

Variables m n p : nat.
Implicit Type A : 'M[R]_(m, n).
Implicit Type B : 'M[R]_(n, p).

Definition mulmxr B A := mulmx A B.
Arguments mulmxr B A /.

Fact mulmxr_is_semilinear B : semilinear (mulmxr B).
Proof.
Admitted.
HB.instance Definition _ (B : 'M_(n, p)) :=
  GRing.isSemilinear.Build R 'M_(m, n) 'M_(m, p) _ (mulmxr B)
    (mulmxr_is_semilinear B).

Definition lin_mulmxr B := lin_mx (mulmxr B).

Fact lin_mulmxr_is_semilinear : semilinear lin_mulmxr.
Proof.
Admitted.
HB.instance Definition _ :=
  GRing.isSemilinear.Build R 'M_(n, p) 'M_(m * n, m * p) _ lin_mulmxr
    lin_mulmxr_is_semilinear.

End Mulmxr.

Section LiftPerm.
(* Block expression of a lifted permutation matrix *)

Variable n : nat.

Definition lift0_mx A : 'M_(1 + n) := block_mx 1 0 0 A.

Lemma lift0_mx_perm s : lift0_mx (perm_mx s) = perm_mx (lift0_perm s).
Proof.
Admitted.

Lemma lift0_mx_is_perm s : is_perm_mx (lift0_mx (perm_mx s)).
Proof.
Admitted.

End LiftPerm.

Lemma exp_block_diag_mx m n (A: 'M_m.
Proof.
Admitted.

End MatrixAlgebra.

Arguments delta_mx {R m n}.
Arguments perm_mx {R n}.
Arguments tperm_mx {R n}.
Arguments pid_mx {R m n}.
Arguments lin_mulmxr {R m n p}.
Prenex Implicits diag_mx is_scalar_mx.
Prenex Implicits mulmx mxtrace.

Arguments mul_delta_mx {R m n p}.
Arguments mulmxr {_ _ _ _} B A /.

#[global] Hint Extern 0 (is_true (is_diag_mx (scalar_mx _))) =>
  apply: scalar_mx_is_diag : core.
#[global] Hint Extern 0 (is_true (is_trig_mx (scalar_mx _))) =>
  apply: scalar_mx_is_trig : core.
#[global] Hint Extern 0 (is_true (is_diag_mx (diag_mx _))) =>
  apply: diag_mx_is_diag : core.
#[global] Hint Extern 0 (is_true (is_trig_mx (diag_mx _))) =>
  apply: diag_mx_is_trig : core.

Notation "a %:M" := (scalar_mx a) : ring_scope.
Notation "A *m B" := (mulmx A B) : ring_scope.

(* Non-commutative transpose requires multiplication in the converse ring.   *)
Lemma trmx_mul_rev (R : pzSemiRingType) m n p
    (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)) :
  (A *m B)^T = (B : 'M[R^c]_(n, p))^T *m (A : 'M[R^c]_(m, n))^T.
Proof.
Admitted.

HB.instance Definition _ (R : pzRingType) m n :=
  GRing.LSemiModule.on 'M[R]_(m, n).
HB.instance Definition _ (R : pzRingType) n := GRing.PzSemiRing.on 'M[R]_n.

Section MatrixNzSemiRing.

Variables (R : nzSemiRingType) (n' : nat).
Local Notation n := n'.+1.

Lemma matrix_nonzero1 : 1%:M != 0 :> 'M[R]_n.
Proof.
Admitted.

HB.instance Definition _ :=
  GRing.PzSemiRing_isNonZero.Build 'M[R]_n matrix_nonzero1.

End MatrixNzSemiRing.

HB.instance Definition _ (R : nzRingType) n := GRing.NzSemiRing.on 'M[R]_n.+1.

HB.instance Definition _ (M : countNmodType) m n :=
  [Countable of 'M[M]_(m, n) by <:].
HB.instance Definition _ (M : countZmodType) m n :=
  [Countable of 'M[M]_(m, n) by <:].
HB.instance Definition _ (R : countNzSemiRingType) n :=
  [Countable of 'M[R]_n.+1 by <:].
HB.instance Definition _ (R : countNzRingType) n :=
  [Countable of 'M[R]_n.+1 by <:].

HB.instance Definition _ (V : finNmodType) (m n : nat) :=
  [Finite of 'M[V]_(m, n) by <:].
HB.instance Definition _ (V : finZmodType) (m n : nat) :=
  [Finite of 'M[V]_(m, n) by <:].
#[compress_coercions]
HB.instance Definition _ (V : finZmodType) (m n : nat) :=
  [finGroupMixin of 'M[V]_(m, n) for +%R].
#[compress_coercions]
HB.instance Definition _ (R : finNzSemiRingType) n :=
  [Finite of 'M[R]_n.+1 by <:].
#[compress_coercions]
HB.instance Definition _ (R : finNzRingType) (m n : nat) :=
  FinRing.Zmodule.on 'M[R]_(m, n).
#[compress_coercions]
HB.instance Definition _ (R : finNzRingType) n := [Finite of 'M[R]_n.+1 by <:].

(* Parametricity over the algebra structure. *)
Section MapSemiRingMatrix.

Variables (aR rR : pzSemiRingType) (f : {rmorphism aR -> rR}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Section FixedSize.

Variables m n p : nat.
Implicit Type A : 'M[aR]_(m, n).

Lemma map_mxZ a A : (a *: A)^f = f a *: A^f.
Proof.
Admitted.

Lemma map_mxM A B : (A *m B)^f = A^f *m B^f :> 'M_(m, p).
Proof.
Admitted.

Lemma map_delta_mx i j : (delta_mx i j)^f = delta_mx i j :> 'M_(m, n).
Proof.
Admitted.

Lemma map_diag_mx d : (diag_mx d)^f = diag_mx d^f :> 'M_n.
Proof.
Admitted.

Lemma map_scalar_mx a : a%:M^f = (f a)%:M :> 'M_n.
Proof.
Admitted.

Lemma map_mx1 : 1%:M^f = 1%:M :> 'M_n.
Proof.
Admitted.

Lemma map_perm_mx (s : 'S_n) : (perm_mx s)^f = perm_mx s.
Proof.
Admitted.

Lemma map_tperm_mx (i1 i2 : 'I_n) : (tperm_mx i1 i2)^f = tperm_mx i1 i2.
Proof.
Admitted.

Lemma map_pid_mx r : (pid_mx r)^f = pid_mx r :> 'M_(m, n).
Proof.
Admitted.

Lemma trace_map_mx (A : 'M_n) : \tr A^f = f (\tr A).
Proof.
Admitted.

End FixedSize.

Lemma map_lin1_mx m n (g : 'rV_m -> 'rV_n) gf :
  (forall v, (g v)^f = gf v^f) -> (lin1_mx g)^f = lin1_mx gf.
Proof.
Admitted.

Lemma map_lin_mx m1 n1 m2 n2 (g : 'M_(m1, n1) -> 'M_(m2, n2)) gf :
  (forall A, (g A)^f = gf A^f) -> (lin_mx g)^f = lin_mx gf.
Proof.
Admitted.

Fact map_mx_is_monoid_morphism n : monoid_morphism (map_mx f : 'M_n -> 'M_n).
Proof.
Admitted.
#[deprecated(since="mathcomp 2.5.0", use=map_mx_is_monoid_morphism)]
Definition map_mx_is_multiplicative := map_mx_is_monoid_morphism.
HB.instance Definition _ n :=
  GRing.isMonoidMorphism.Build 'M[aR]_n 'M[rR]_n (map_mx f)
    (map_mx_is_monoid_morphism n).

End MapSemiRingMatrix.

Section CommMx.
(***********************************************************************)
(* Commutation property specialized to 'M[R]_n                         *)
(*                                                                     *)
(* GRing.comm is bound to (non trivial) rings, and matrices form a     *)
(* (non trivial) ring only when they are square and of manifestly      *)
(* positive size. However during proofs in endomorphism reduction, we  *)
(* take restrictions, which are matrices of size #|V| (with V a matrix *)
(* space) and it becomes cumbersome to state commutation between       *)
(* restrictions, unless we relax the setting, and this relaxation      *)
(* corresponds to comm_mx A B := A *m B = B *m A.                      *)
(* As witnessed by comm_mxE, when A and B have type 'M_n.+1,           *)
(*   comm_mx A B is convertible to GRing.comm A B.                     *)
(* The boolean version comm_mxb is designed to be used with seq.allrel *)
(***********************************************************************)

Context {R : pzSemiRingType} {n : nat}.
Implicit Types (f g p : 'M[R]_n) (fs : seq 'M[R]_n) (d : 'rV[R]_n) (I : Type).

Definition comm_mx  f g : Prop := f *m g =  g *m f.
Definition comm_mxb f g : bool := f *m g == g *m f.

Lemma comm_mx_sym f g : comm_mx f g -> comm_mx g f.
Proof.
Admitted.

Lemma comm_mx_refl f : comm_mx f f.
Proof.
Admitted.

Lemma comm_mx0 f : comm_mx f 0.
Proof.
Admitted.
Lemma comm0mx f : comm_mx 0 f.
Proof.
Admitted.

Lemma comm_mx1 f : comm_mx f 1%:M.
Proof.
Admitted.

Lemma comm1mx f : comm_mx 1%:M f.
Proof.
Admitted.

Hint Resolve comm_mx0 comm0mx comm_mx1 comm1mx : core.

Lemma comm_mxD f g g' : comm_mx f g -> comm_mx f g' -> comm_mx f (g + g').
Proof.
Admitted.

Lemma comm_mxM f g g' : comm_mx f g -> comm_mx f g' -> comm_mx f (g *m g').
Proof.
Admitted.

Lemma comm_mx_sum I (s : seq I) (P : pred I) (F : I -> 'M[R]_n) (f : 'M[R]_n) :
  (forall i : I, P i -> comm_mx f (F i)) -> comm_mx f (\sum_(i <- s | P i) F i).
Proof.
Admitted.

Lemma comm_mxP f g : reflect (comm_mx f g) (comm_mxb f g).
Proof.
Admitted.

Notation all_comm_mx fs := (all2rel comm_mxb fs).

Lemma all_comm_mxP fs :
  reflect {in fs &, forall f g, f *m g = g *m f} (all_comm_mx fs).
Proof.
Admitted.

Lemma all_comm_mx1 f : all_comm_mx [:: f].
Proof.
Admitted.

Lemma all_comm_mx2P f g : reflect (f *m g = g *m f) (all_comm_mx [:: f; g]).
Proof.
Admitted.

Lemma all_comm_mx_cons f fs :
  all_comm_mx (f :: fs) = all (comm_mxb f) fs && all_comm_mx fs.
Proof.
Admitted.

Lemma comm_mxE : comm_mx = @GRing.
Proof.
Admitted.

End CommMx.
Notation all_comm_mx := (allrel comm_mxb).

Section ComMatrix.
(* Lemmas for matrices with coefficients in a commutative ring *)
Variable R : comPzSemiRingType.

Section AssocLeft.

Variables m n p : nat.
Implicit Type A : 'M[R]_(m, n).
Implicit Type B : 'M[R]_(n, p).

Lemma trmx_mul A B : (A *m B)^T = B^T *m A^T.
Proof.
Admitted.

Lemma scalemxAr a A B : a *: (A *m B) = A *m (a *: B).
Proof.
Admitted.

Fact mulmx_is_scalable A : scalable (@mulmx _ m n p A).
Proof.
Admitted.
HB.instance Definition _ A :=
  GRing.isScalable.Build R 'M[R]_(n, p) 'M[R]_(m, p) *:%R (mulmx A)
    (mulmx_is_scalable A).

Definition lin_mulmx A : 'M[R]_(n * p, m * p) := lin_mx (mulmx A).

Fact lin_mulmx_is_semilinear : semilinear lin_mulmx.
Proof.
Admitted.
HB.instance Definition _ :=
  GRing.isSemilinear.Build R 'M[R]_(m, n) 'M[R]_(n * p, m * p) _ lin_mulmx
    lin_mulmx_is_semilinear.

End AssocLeft.

Section LinMulRow.

Variables m n : nat.

Definition lin_mul_row u : 'M[R]_(m * n, n) := lin1_mx (mulmx u \o vec_mx).

Fact lin_mul_row_is_semilinear : semilinear lin_mul_row.
Proof.
Admitted.
HB.instance Definition _ := GRing.isSemilinear.Build R _ _ _ lin_mul_row
  lin_mul_row_is_semilinear.

Lemma mul_vec_lin_row A u : mxvec A *m lin_mul_row u = u *m A.
Proof.
Admitted.

End LinMulRow.

Lemma diag_mxC n (d e : 'rV[R]_n) :
  diag_mx d *m diag_mx e = diag_mx e *m diag_mx d.
Proof.
Admitted.

Lemma diag_mx_comm n (d e : 'rV[R]_n) : comm_mx (diag_mx d) (diag_mx e).
Proof.
Admitted.

Lemma scalar_mxC m n a (A : 'M[R]_(m, n)) : A *m a%:M = a%:M *m A.
Proof.
Admitted.

Lemma comm_mx_scalar n a (A : 'M[R]_n) : comm_mx A a%:M.
Proof.
Admitted.

Lemma comm_scalar_mx n a (A : 'M[R]_n) : comm_mx a%:M A.
Proof.
Admitted.

Lemma mxtrace_mulC m n (A : 'M[R]_(m, n)) B : \tr (A *m B) = \tr (B *m A).
Proof.
Admitted.

Lemma mxvec_dotmul m n (A : 'M[R]_(m, n)) u v :
  mxvec (u^T *m v) *m (mxvec A)^T = u *m A *m v^T.
Proof.
Admitted.

Lemma mul_mx_scalar m n a (A : 'M[R]_(m, n)) : A *m a%:M = a *: A.
Proof.
Admitted.

End ComMatrix.

HB.instance Definition _ (R : comPzSemiRingType) (n : nat) :=
  GRing.LSemiAlgebra_isSemiAlgebra.Build R 'M[R]_n (fun k => scalemxAr k).

HB.instance Definition _ (R : comPzRingType) (n : nat) :=
  GRing.PzSemiAlgebra.on 'M[R]_n.

HB.instance Definition _ (R : comNzSemiRingType) (n' : nat) :=
  GRing.PzSemiAlgebra.on 'M[R]_n'.+1.

HB.instance Definition _ (R : comNzRingType) (n' : nat) :=
  GRing.PzAlgebra.on 'M[R]_n'.+1.

HB.instance Definition _ (R : finComNzRingType) (n' : nat) :=
  [Finite of 'M[R]_n'.+1 by <:].

Arguments lin_mulmx {R m n p} A.
Arguments lin_mul_row {R m n} u.
Arguments diag_mx_comm {R n}.
Arguments comm_mx_scalar {R n}.
Arguments comm_scalar_mx {R n}.

#[global] Hint Resolve comm_mx_scalar comm_scalar_mx : core.

Section MatrixAlgebra.

Variable R : pzRingType.

(* Diagonal matrices *)

#[deprecated(since="mathcomp 2.5.0", use=linearP)]
Fact diag_mx_is_linear n : linear (@diag_mx R n).
Proof.
Admitted.

(* Scalar matrix *)

Lemma mulmxN m n p (A : 'M[R]_(m, n)) (B : 'M_(n, p)) : A *m (- B) = - (A *m B).
Proof.
Admitted.

Lemma mulNmx m n p (A : 'M[R]_(m, n)) (B : 'M_(n, p)) : - A *m B = - (A *m B).
Proof.
Admitted.

Lemma mulmxBl m n p (A1 A2 : 'M[R]_(m, n)) (B : 'M_(n, p)) :
  (A1 - A2) *m B = A1 *m B - A2 *m B.
Proof.
Admitted.

Lemma mulmxBr m n p (A : 'M[R]_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *m (B1 - B2) = A *m B1 - A *m B2.
Proof.
Admitted.

(* Partial identity matrix (used in rank decomposition). *)

Definition copid_mx {n} r : 'M[R]_n := 1%:M - pid_mx r.

Lemma mul_copid_mx_pid m n r :
  r <= m -> copid_mx r *m pid_mx r = 0 :> 'M_(m, n).
Proof.
Admitted.

Lemma mul_pid_mx_copid m n r :
  r <= n -> pid_mx r *m copid_mx r = 0 :> 'M_(m, n).
Proof.
Admitted.

Lemma copid_mx_id n r : r <= n -> copid_mx r *m copid_mx r = copid_mx r :> 'M_n.
Proof.
Admitted.

#[deprecated(since="mathcomp 2.5.0", use=linearP)]
Fact mulmxr_is_linear m n p B : linear (@mulmxr R m n p B).
Proof.
Admitted.

#[deprecated(since="mathcomp 2.5.0", use=linearP)]
Fact lin_mulmxr_is_linear m n p : linear (@lin_mulmxr R m n p).
Proof.
Admitted.

#[deprecated(since="mathcomp 2.5.0", use=scalarP)]
Fact mxtrace_is_scalar n : scalar (@mxtrace R n).
Proof.
Admitted.

(* Determinants and adjugates are defined here, but most of their properties *)
(* only hold for matrices over a commutative ring, so their theory is        *)
(* deferred to that section.                                                 *)

(* The determinant, in one line with the Leibniz Formula *)
Definition determinant n (A : 'M_n) : R :=
  \sum_(s : 'S_n) (-1) ^+ s * \prod_i A i (s i).

(* The cofactor of a matrix on the indexes i and j *)
Definition cofactor n A (i j : 'I_n) : R :=
  (-1) ^+ (i + j) * determinant (row' i (col' j A)).

(* The adjugate matrix : defined as the transpose of the matrix of cofactors *)
Fact adjugate_key : unit.
Proof.
Admitted.
Definition adjugate n (A : 'M_n) := \matrix[adjugate_key]_(i, j) cofactor A j i.

End MatrixAlgebra.

Arguments copid_mx {R n}.
Prenex Implicits determinant cofactor adjugate.

Notation "'\det' A" := (determinant A) : ring_scope.
Notation "'\adj' A" := (adjugate A) : ring_scope.

(* Parametricity over the algebra structure. *)
Section MapRingMatrix.

Variables (aR rR : pzRingType) (f : {rmorphism aR -> rR}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Section FixedSize.

Variables m n p : nat.
Implicit Type A : 'M[aR]_(m, n).

Lemma det_map_mx n' (A : 'M_n') : \det A^f = f (\det A).
Proof.
Admitted.

Lemma cofactor_map_mx (A : 'M_n) i j : cofactor A^f i j = f (cofactor A i j).
Proof.
Admitted.

Lemma map_mx_adj (A : 'M_n) : (\adj A)^f = \adj A^f.
Proof.
Admitted.

End FixedSize.

Lemma map_copid_mx n r : (copid_mx r)^f = copid_mx r :> 'M_n.
Proof.
Admitted.

End MapRingMatrix.

Section CommMx.
(***********************************************************************)
(************* Commutation property specialized to 'M[R]_n *************)
(***********************************************************************)
(* See comment on top of NzSemiRing section CommMx above.                *)
(***********************************************************************)

Context {R : pzRingType} {n : nat}.
Implicit Types (f g p : 'M[R]_n) (fs : seq 'M[R]_n) (d : 'rV[R]_n) (I : Type).

Lemma comm_mxN f g : comm_mx f g -> comm_mx f (- g).
Proof.
Admitted.

Lemma comm_mxN1 f : comm_mx f (- 1%:M).
Proof.
Admitted.

Lemma comm_mxB f g g' : comm_mx f g -> comm_mx f g' -> comm_mx f (g - g').
Proof.
Admitted.

End CommMx.

(* Lemmas for matrices with coefficients in a commutative ring *)
Section ComMatrix.
Variable R : comPzRingType.

#[deprecated(since="mathcomp 2.5.0", use=linearP)]
Fact lin_mulmx_is_linear m n p : linear (@lin_mulmx R m n p).
Proof.
Admitted.

#[deprecated(since="mathcomp 2.5.0", use=linearP)]
Fact lin_mul_row_is_linear m n : linear (@lin_mul_row R m n).
Proof.
Admitted.

(* The theory of determinants *)

Lemma determinant_multilinear n (A B C : 'M[R]_n) i0 b c :
    row i0 A = b *: row i0 B + c *: row i0 C ->
    row' i0 B = row' i0 A ->
    row' i0 C = row' i0 A ->
  \det A = b * \det B + c * \det C.
Proof.
Admitted.

Lemma determinant_alternate n (A : 'M[R]_n) i1 i2 :
  i1 != i2 -> A i1 =1 A i2 -> \det A = 0.
Proof.
Admitted.

Lemma det_tr n (A : 'M[R]_n) : \det A^T = \det A.
Proof.
Admitted.

Lemma det_perm n (s : 'S_n) : \det (perm_mx s) = (-1) ^+ s :> R.
Proof.
Admitted.

Lemma det1 n : \det (1%:M : 'M[R]_n) = 1.
Proof.
Admitted.

Lemma det_mx00 (A : 'M[R]_0) : \det A = 1.
Proof.
Admitted.

Lemma detZ n a (A : 'M[R]_n) : \det (a *: A) = a ^+ n * \det A.
Proof.
Admitted.

Lemma det0 n' : \det (0 : 'M[R]_n'.
Proof.
Admitted.

Lemma det_scalar n a : \det (a%:M : 'M[R]_n) = a ^+ n.
Proof.
Admitted.

Lemma det_scalar1 a : \det (a%:M : 'M[R]_1) = a.
Proof.
Admitted.

Lemma det_mx11  (M : 'M[R]_1) : \det M = M 0 0.
Proof.
Admitted.

Lemma det_mulmx n (A B : 'M[R]_n) : \det (A *m B) = \det A * \det B.
Proof.
Admitted.

Lemma detM n' (A B : 'M[R]_n'.
Proof.
Admitted.

(* Laplace expansion lemma *)
Lemma expand_cofactor n (A : 'M[R]_n) i j :
  cofactor A i j =
    \sum_(s : 'S_n | s i == j) (-1) ^+ s * \prod_(k | i != k) A k (s k).
Proof.
Admitted.

Lemma expand_det_row n (A : 'M[R]_n) i0 :
  \det A = \sum_j A i0 j * cofactor A i0 j.
Proof.
Admitted.

Lemma cofactor_tr n (A : 'M[R]_n) i j : cofactor A^T i j = cofactor A j i.
Proof.
Admitted.

Lemma cofactorZ n a (A : 'M[R]_n) i j :
  cofactor (a *: A) i j = a ^+ n.
Proof.
Admitted.

Lemma expand_det_col n (A : 'M[R]_n) j0 :
  \det A = \sum_i (A i j0 * cofactor A i j0).
Proof.
Admitted.

Lemma trmx_adj n (A : 'M[R]_n) : (\adj A)^T = \adj A^T.
Proof.
Admitted.

Lemma adjZ n a (A : 'M[R]_n) : \adj (a *: A) = a^+n.
Proof.
Admitted.

(* Cramer Rule : adjugate on the left *)
Lemma mul_mx_adj n (A : 'M[R]_n) : A *m \adj A = (\det A)%:M.
Proof.
Admitted.

(* Cramer rule : adjugate on the right *)
Lemma mul_adj_mx n (A : 'M[R]_n) : \adj A *m A = (\det A)%:M.
Proof.
Admitted.

Lemma adj1 n : \adj (1%:M) = 1%:M :> 'M[R]_n.
Proof.
Admitted.

(* Left inverses are right inverses. *)
Lemma mulmx1C n (A B : 'M[R]_n) : A *m B = 1%:M -> B *m A = 1%:M.
Proof.
Admitted.

Lemma det_ublock n1 n2 Aul (Aur : 'M[R]_(n1, n2)) Adr :
  \det (block_mx Aul Aur 0 Adr) = \det Aul * \det Adr.
Proof.
Admitted.

Lemma det_lblock n1 n2 Aul (Adl : 'M[R]_(n2, n1)) Adr :
  \det (block_mx Aul 0 Adl Adr) = \det Aul * \det Adr.
Proof.
Admitted.

Lemma det_trig n (A : 'M[R]_n) : is_trig_mx A -> \det A = \prod_(i < n) A i i.
Proof.
Admitted.

Lemma det_diag n (d : 'rV[R]_n) : \det (diag_mx d) = \prod_i d 0 i.
Proof.
Admitted.

End ComMatrix.

Arguments lin_mul_row {R m n} u.
Arguments lin_mulmx {R m n p} A.

(* Only tall matrices have inverses. *)
Lemma mulmx1_min (R : comNzRingType) m n (A : 'M[R]_(m, n)) B :
  A *m B = 1%:M -> m <= n.
Proof.
Admitted.

(*****************************************************************************)
(********************** Matrix unit ring and inverse matrices ****************)
(*****************************************************************************)

Section MatrixInv.

Variables R : comUnitRingType.

Section Defs.

Variable n : nat.
Implicit Type A : 'M[R]_n.

Definition unitmx : pred 'M[R]_n := fun A => \det A \is a GRing.unit.
Definition invmx A := if A \in unitmx then (\det A)^-1 *: \adj A else A.

Lemma unitmxE A : (A \in unitmx) = (\det A \is a GRing.
Proof.
Admitted.

Lemma unitmx1 : 1%:M \in unitmx.
Proof.
Admitted.

Lemma unitmx_perm s : perm_mx s \in unitmx.
Proof.
Admitted.

Lemma unitmx_tr A : (A^T \in unitmx) = (A \in unitmx).
Proof.
Admitted.

Lemma unitmxZ a A : a \is a GRing.
Proof.
Admitted.

Lemma invmx1 : invmx 1%:M = 1%:M.
Proof.
Admitted.

Lemma invmxZ a A : a *: A \in unitmx -> invmx (a *: A) = a^-1 *: invmx A.
Proof.
Admitted.

Lemma invmx_scalar a : invmx a%:M = a^-1%:M.
Proof.
Admitted.

Lemma mulVmx : {in unitmx, left_inverse 1%:M invmx mulmx}.
Proof.
Admitted.

Lemma mulmxV : {in unitmx, right_inverse 1%:M invmx mulmx}.
Proof.
Admitted.

Lemma mulKmx m : {in unitmx, @left_loop _ 'M_(n, m) invmx mulmx}.
Proof.
Admitted.

Lemma mulKVmx m : {in unitmx, @rev_left_loop _ 'M_(n, m) invmx mulmx}.
Proof.
Admitted.

Lemma mulmxK m : {in unitmx, @right_loop 'M_(m, n) _ invmx mulmx}.
Proof.
Admitted.

Lemma mulmxKV m : {in unitmx, @rev_right_loop 'M_(m, n) _ invmx mulmx}.
Proof.
Admitted.

Lemma det_inv A : \det (invmx A) = (\det A)^-1.
Proof.
Admitted.

Lemma unitmx_inv A : (invmx A \in unitmx) = (A \in unitmx).
Proof.
Admitted.

Lemma unitmx_mul A B : (A *m B \in unitmx) = (A \in unitmx) && (B \in unitmx).
Proof.
Admitted.

Lemma trmx_inv (A : 'M_n) : (invmx A)^T = invmx (A^T).
Proof.
Admitted.

Lemma invmxK : involutive invmx.
Proof.
Admitted.

Lemma mulmx1_unit A B : A *m B = 1%:M -> A \in unitmx /\ B \in unitmx.
Proof.
Admitted.

Lemma intro_unitmx A B : B *m A = 1%:M /\ A *m B = 1%:M -> unitmx A.
Proof.
Admitted.

Lemma invmx_out : {in [predC unitmx], invmx =1 id}.
Proof.
Admitted.

End Defs.

Variable n' : nat.
Local Notation n := n'.+1.

HB.instance Definition _ := GRing.NzRing_hasMulInverse.Build 'M[R]_n
  (@mulVmx n) (@mulmxV n) (@intro_unitmx n) (@invmx_out n).

(* Lemmas requiring that the coefficients are in a unit ring *)

Lemma detV (A : 'M_n) : \det A^-1 = (\det A)^-1.
Proof.
Admitted.

Lemma unitr_trmx (A : 'M_n) : (A^T  \is a GRing.
Proof.
Admitted.

Lemma trmxV (A : 'M_n) : A^-1^T = (A^T)^-1.
Proof.
Admitted.

Lemma perm_mxV (s : 'S_n) : perm_mx s^-1 = (perm_mx s)^-1.
Proof.
Admitted.

Lemma is_perm_mxV (A : 'M_n) : is_perm_mx A^-1 = is_perm_mx A.
Proof.
Admitted.

End MatrixInv.

Prenex Implicits unitmx invmx invmxK.

Lemma block_diag_mx_unit (R : comUnitRingType) n1 n2
      (Aul : 'M[R]_n1) (Adr : 'M[R]_n2) :
  (block_mx Aul 0 0 Adr \in unitmx) = (Aul \in unitmx) && (Adr \in unitmx).
Proof.
Admitted.

Lemma invmx_block_diag (R : comUnitRingType) n1 n2
     (Aul : 'M[R]_n1) (Adr : 'M[R]_n2) :
  block_mx Aul 0 0 Adr \in unitmx ->
  invmx (block_mx Aul 0 0 Adr) = block_mx (invmx Aul) 0 0 (invmx Adr).
Proof.
Admitted.

HB.instance Definition _ (R : countComUnitRingType) (n' : nat) :=
  [Countable of 'M[R]_n'.+1 by <:].

HB.instance Definition _ (n : nat) (R : finComUnitRingType) :=
  [Finite of 'M[R]_n.+1 by <:].
(* Finite inversible matrices and the general linear group. *)
Section FinUnitMatrix.

Variable n : nat.

Definition GLtype (R : finComUnitRingType) := {unit 'M[R]_n.-1.+1}.

Coercion GLval R (u : GLtype R) : 'M[R]_n.-1.+1 :=
  let: FinRing.Unit A _ := u in A.

End FinUnitMatrix.

Bind Scope group_scope with GLtype.
Arguments GLtype n%_N R%_type.
Arguments GLval {n%_N R} u%_g.

Notation "{ ''GL_' n [ R ] }" := (GLtype n R) : type_scope.

Notation "{ ''GL_' n ( p ) }" := {'GL_n['F_p]} : type_scope.

HB.instance Definition _ (n : nat) (R : finComUnitRingType) :=
  [isSub of {'GL_n[R]} for GLval].

Section GL_unit.

Variables (n : nat) (R : finComUnitRingType).

HB.instance Definition _ := [Finite of {'GL_n[R]} by <:].
HB.instance Definition _ := FinGroup.on {'GL_n[R]}.

Definition GLgroup := [set: {'GL_n[R]}].
Canonical GLgroup_group := Eval hnf in [group of GLgroup].

Implicit Types u v : {'GL_n[R]}.

Lemma GL_1E : GLval 1 = 1.
Proof.
Admitted.
Lemma GL_VE u : GLval u^-1 = (GLval u)^-1.
Proof.
Admitted.
Lemma GL_VxE u : GLval u^-1 = invmx u.
Proof.
Admitted.
Lemma GL_ME u v : GLval (u * v) = GLval u * GLval v.
Proof.
Admitted.
Lemma GL_MxE u v : GLval (u * v) = u *m v.
Proof.
Admitted.
Lemma GL_unit u : GLval u \is a GRing.
Proof.
Admitted.
Lemma GL_unitmx u : val u \in unitmx.
Proof.
Admitted.

Lemma GL_det u : \det u != 0.
Proof.
Admitted.

End GL_unit.

Arguments GLgroup n%_N R%_type.
Arguments GLgroup_group n%_N R%_type.

Notation "''GL_' n [ R ]" := (GLgroup n R)
  (n at level 2, format "''GL_' n [ R ]") : group_scope.
Notation "''GL_' n ( p )" := 'GL_n['F_p]
  (p at level 10, format "''GL_' n ( p )") : group_scope.
Notation "''GL_' n [ R ]" := (GLgroup_group n R) : Group_scope.
Notation "''GL_' n ( p )" := (GLgroup_group n 'F_p) : Group_scope.

(*****************************************************************************)
(********************** Matrices over a domain *******************************)
(*****************************************************************************)

Section MatrixDomain.

Variable R : idomainType.

Lemma scalemx_eq0 m n a (A : 'M[R]_(m, n)) :
  (a *: A == 0) = (a == 0) || (A == 0).
Proof.
Admitted.

Lemma scalemx_inj m n a :
  a != 0 -> injective ( *:%R a : 'M[R]_(m, n) -> 'M[R]_(m, n)).
Proof.
Admitted.

Lemma det0P n (A : 'M[R]_n) :
  reflect (exists2 v : 'rV[R]_n, v != 0 & v *m A = 0) (\det A == 0).
Proof.
Admitted.

End MatrixDomain.

Arguments det0P {R n A}.

(* Parametricity at the field level (mx_is_scalar, unit and inverse are only *)
(* mapped at this level).                                                    *)
Section MapFieldMatrix.

Variables (aF : fieldType) (rF : comUnitRingType) (f : {rmorphism aF -> rF}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Lemma map_mx_inj {m n} : injective (map_mx f : 'M_(m, n) -> 'M_(m, n)).
Proof.
Admitted.

Lemma map_mx_is_scalar n (A : 'M_n) : is_scalar_mx A^f = is_scalar_mx A.
Proof.
Admitted.

Lemma map_unitmx n (A : 'M_n) : (A^f \in unitmx) = (A \in unitmx).
Proof.
Admitted.

Lemma map_mx_unit n' (A : 'M_n'.
Proof.
Admitted.

Lemma map_invmx n (A : 'M_n) : (invmx A)^f = invmx A^f.
Proof.
Admitted.

Lemma map_mx_inv n' (A : 'M_n'.
Proof.
Admitted.

Lemma map_mx_eq0 m n (A : 'M_(m, n)) : (A^f == 0) = (A == 0).
Proof.
Admitted.

End MapFieldMatrix.

Arguments map_mx_inj {aF rF f m n} [A1 A2] eqA12f : rename.

(*****************************************************************************)
(***************************** LUP decomposition *****************************)
(*****************************************************************************)

Section CormenLUP.

Variable F : fieldType.

(* Decomposition of the matrix A to P A = L U with *)
(*   - P a permutation matrix                      *)
(*   - L a unipotent lower triangular matrix       *)
(*   - U an upper triangular matrix                *)

Fixpoint cormen_lup {n} :=
  match n return let M := 'M[F]_n.+1 in M -> M * M * M with
  | 0 => fun A => (1, 1, A)
  | _.+1 => fun A =>
    let k := odflt 0 [pick k | A k 0 != 0] in
    let A1 : 'M_(1 + _) := xrow 0 k A in
    let P1 : 'M_(1 + _) := tperm_mx 0 k in
    let Schur := ((A k 0)^-1 *: dlsubmx A1) *m ursubmx A1 in
    let: (P2, L2, U2) := cormen_lup (drsubmx A1 - Schur) in
    let P := block_mx 1 0 0 P2 *m P1 in
    let L := block_mx 1 0 ((A k 0)^-1 *: (P2 *m dlsubmx A1)) L2 in
    let U := block_mx (ulsubmx A1) (ursubmx A1) 0 U2 in
    (P, L, U)
  end.

Lemma cormen_lup_perm n (A : 'M_n.
Proof.
Admitted.

Lemma cormen_lup_correct n (A : 'M_n.
Proof.
Admitted.

Lemma cormen_lup_detL n (A : 'M_n.
Proof.
Admitted.

Lemma cormen_lup_lower n A (i j : 'I_n.
Proof.
Admitted.

Lemma cormen_lup_upper n A (i j : 'I_n.
Proof.
Admitted.

End CormenLUP.

Section mxOver.
Section mxOverType.
Context {m n : nat} {T : Type}.
Implicit Types (S : {pred T}).

Definition mxOver_pred (S : {pred T}) :=
  fun M : 'M[T]_(m, n) => [forall i, [forall j, M i j \in S]].
Arguments mxOver_pred _ _ /.
Definition mxOver (S : {pred T}) := [qualify a M | mxOver_pred S M].

Lemma mxOverP {S : {pred T}} {M : 'M[T]__} :
  reflect (forall i j, M i j \in S) (M \is a mxOver S).
Proof.
Admitted.

Lemma mxOverS (S1 S2 : {pred T}) :
  {subset S1 <= S2} -> {subset mxOver S1 <= mxOver S2}.
Proof.
Admitted.

Lemma mxOver_const c S : c \in S -> const_mx c \is a mxOver S.
Proof.
Admitted.

Lemma mxOver_constE c S : (m > 0)%N -> (n > 0)%N ->
  (const_mx c \is a mxOver S) = (c \in S).
Proof.
Admitted.

End mxOverType.

Lemma thinmxOver {n : nat} {T : Type} (M : 'M[T]_(n, 0)) S : M \is a mxOver S.
Proof.
Admitted.

Lemma flatmxOver {n : nat} {T : Type} (M : 'M[T]_(0, n)) S : M \is a mxOver S.
Proof.
Admitted.

Section mxOverZmodule.
Context {M : zmodType} {m n : nat}.
Implicit Types (S : {pred M}).

Lemma mxOver0 S : 0 \in S -> 0 \is a @mxOver m n _ S.
Proof.
Admitted.

Section mxOverAdd.
Variable addS : addrClosed M.
Fact mxOver_add_subproof : addr_closed (@mxOver m n _ addS).
Proof.
Admitted.
HB.instance Definition _ :=
  GRing.isAddClosed.Build 'M[M]_(m, n) (mxOver_pred addS)
    mxOver_add_subproof.
End mxOverAdd.

Section mxOverOpp.
Variable oppS : opprClosed M.
Fact mxOver_opp_subproof : oppr_closed (@mxOver m n _ oppS).
Proof.
Admitted.
HB.instance Definition _ :=
  GRing.isOppClosed.Build 'M[M]_(m, n) (mxOver_pred oppS)
    mxOver_opp_subproof.
End mxOverOpp.

HB.instance Definition _ (zmodS : zmodClosed M) :=
  GRing.OppClosed.on (mxOver_pred zmodS).

End mxOverZmodule.

Section mxOverRing.
Context {R : pzSemiRingType} {m n : nat}.

Lemma mxOver_scalar S c : 0 \in S -> c \in S -> c%:M \is a @mxOver n n R S.
Proof.
Admitted.

Lemma mxOver_scalarE S c : (n > 0)%N ->
  (c%:M \is a @mxOver n n R S) = ((n > 1) ==> (0 \in S)) && (c \in S).
Proof.
Admitted.

Lemma mxOverZ (S : mulrClosed R) :
  {in S & mxOver S, forall a : R, forall v : 'M[R]_(m, n),
     a *: v \is a mxOver S}.
Proof.
Admitted.

Lemma mxOver_diag (S : {pred R}) k (D : 'rV[R]_k) :
   0 \in S -> D \is a mxOver S -> diag_mx D \is a mxOver S.
Proof.
Admitted.

Lemma mxOver_diagE (S : {pred R}) k (D : 'rV[R]_k) : k > 0 ->
  (diag_mx D \is a mxOver S) = ((k > 1) ==> (0 \in S)) && (D \is a mxOver S).
Proof.
Admitted.

Lemma mxOverM (S : semiringClosed R) p q r : {in mxOver S & mxOver S,
  forall u : 'M[R]_(p, q), forall v : 'M[R]_(q, r), u *m v \is a mxOver S}.
Proof.
Admitted.

End mxOverRing.

Section mxRingOver.
Context {R : pzSemiRingType} {n : nat} (S : semiringClosed R).

Fact mxOver_mul_subproof : mulr_closed (@mxOver n n _ S).
Proof.
Admitted.
HB.instance Definition _ := GRing.isMulClosed.Build _ (mxOver_pred S)
  mxOver_mul_subproof.

End mxRingOver.

HB.instance Definition _ {R : pzRingType} {n : nat} (S : subringClosed R) :=
  GRing.MulClosed.on (@mxOver_pred n n _ S).

End mxOver.

Section BlockMatrix.
Import tagnat.
Context {T : Type} {p q : nat} {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}.
Notation sp := (\sum_i p_ i)%N.
Notation sq := (\sum_i q_ i)%N.
Implicit Type (s : 'I_sp) (t : 'I_sq).

Definition mxblock (B_ : forall i j, 'M[T]_(p_ i, q_ j)) :=
  \matrix_(j, k) B_ (sig1 j) (sig1 k) (sig2 j) (sig2 k).
Local Notation "\mxblock_ ( i , j ) E" := (mxblock (fun i j => E)) : ring_scope.

Definition mxrow m (B_ : forall j, 'M[T]_(m, q_ j)) :=
  \matrix_(j, k) B_ (sig1 k) j (sig2 k).
Local Notation "\mxrow_ i E" := (mxrow (fun i => E)) : ring_scope.

Definition mxcol n (B_ : forall i, 'M[T]_(p_ i, n)) :=
  \matrix_(j, k) B_ (sig1 j) (sig2 j) k.
Local Notation "\mxcol_ i E" := (mxcol (fun i => E)) : ring_scope.

Definition submxblock (A : 'M[T]_(sp, sq)) i j := mxsub  (Rank i) (Rank j) A.
Definition submxrow m (A : 'M[T]_(m, sq))    j := colsub          (Rank j) A.
Definition submxcol n (A : 'M[T]_(sp, n))  i   := rowsub (Rank i)          A.

Lemma mxblockEh B_ : \mxblock_(i, j) B_ i j = \mxrow_j \mxcol_i B_ i j.
Proof.
Admitted.

Lemma mxblockEv B_ : \mxblock_(i, j) B_ i j = \mxcol_i \mxrow_j B_ i j.
Proof.
Admitted.

Lemma submxblockEh A i j : submxblock A i j = submxcol (submxrow A j) i.
Proof.
Admitted.

Lemma submxblockEv A i j : submxblock A i j = submxrow (submxcol A i) j.
Proof.
Admitted.

Lemma mxblockK B_ i j : submxblock (\mxblock_(i, j) B_ i j) i j = B_ i j.
Proof.
Admitted.

Lemma mxrowK m B_ j : @submxrow m (\mxrow_j B_ j) j = B_ j.
Proof.
Admitted.

Lemma mxcolK n B_ i : @submxcol n (\mxcol_i B_ i) i = B_ i.
Proof.
Admitted.

Lemma submxrow_matrix B_ j :
  submxrow (\mxblock_(i, j) B_ i j) j = \mxcol_i B_ i j.
Proof.
Admitted.

Lemma submxcol_matrix B_ i :
  submxcol (\mxblock_(i, j) B_ i j) i = \mxrow_j B_ i j.
Proof.
Admitted.

Lemma submxblockK A : \mxblock_(i, j) (submxblock A i j) = A.
Proof.
Admitted.

Lemma submxrowK m (A : 'M[T]_(m, sq)) : \mxrow_j (submxrow A j) = A.
Proof.
Admitted.

Lemma submxcolK n (A : 'M[T]_(sp, n)) : \mxcol_i (submxcol A i) = A.
Proof.
Admitted.

Lemma mxblockP A B :
  (forall i j, submxblock A i j = submxblock B i j) <-> A = B.
Proof.
Admitted.

Lemma mxrowP m (A B : 'M_(m, sq)) :
  (forall j, submxrow A j = submxrow B j) <-> A = B.
Proof.
Admitted.

Lemma mxcolP n (A B : 'M_(sp, n)) :
  (forall i, submxcol A i = submxcol B i) <-> A = B.
Proof.
Admitted.

Lemma eq_mxblockP A_ B_ :
  (forall i j, A_ i j = B_ i j) <->
  (\mxblock_(i, j) A_ i j = \mxblock_(i, j) B_ i j).
Proof.
Admitted.

Lemma eq_mxblock A_ B_ :
  (forall i j, A_ i j = B_ i j) ->
  (\mxblock_(i, j) A_ i j = \mxblock_(i, j) B_ i j).
Proof.
Admitted.

Lemma eq_mxrowP m (A_ B_ : forall j, 'M[T]_(m, q_ j)) :
  (forall j, A_ j = B_ j) <-> (\mxrow_j A_ j = \mxrow_j B_ j).
Proof.
Admitted.

Lemma eq_mxrow m (A_ B_ : forall j, 'M[T]_(m, q_ j)) :
  (forall j, A_ j = B_ j) -> (\mxrow_j A_ j = \mxrow_j B_ j).
Proof.
Admitted.

Lemma eq_mxcolP n (A_ B_ : forall i, 'M[T]_(p_ i, n)) :
  (forall i, A_ i = B_ i) <-> (\mxcol_i A_ i = \mxcol_i B_ i).
Proof.
Admitted.

Lemma eq_mxcol n (A_ B_ : forall i, 'M[T]_(p_ i, n)) :
  (forall i, A_ i = B_ i) -> (\mxcol_i A_ i = \mxcol_i B_ i).
Proof.
Admitted.

Lemma row_mxrow m (B_ : forall j, 'M[T]_(m, q_ j)) i :
  row i (\mxrow_j B_ j) = \mxrow_j (row i (B_ j)).
Proof.
Admitted.

Lemma col_mxrow m (B_ : forall j, 'M[T]_(m, q_ j)) j :
  col j (\mxrow_j B_ j) = col (sig2 j) (B_ (sig1 j)).
Proof.
Admitted.

Lemma row_mxcol n (B_ : forall i, 'M[T]_(p_ i, n)) i :
  row i (\mxcol_i B_ i) = row (sig2 i) (B_ (sig1 i)).
Proof.
Admitted.

Lemma col_mxcol n (B_ : forall i, 'M[T]_(p_ i, n)) j :
  col j (\mxcol_i B_ i) = \mxcol_i (col j (B_ i)).
Proof.
Admitted.

Lemma row_mxblock B_ i :
  row i (\mxblock_(i, j) B_ i j) = \mxrow_j row (sig2 i) (B_ (sig1 i) j).
Proof.
Admitted.

Lemma col_mxblock B_ j :
  col j (\mxblock_(i, j) B_ i j) = \mxcol_i col (sig2 j) (B_ i (sig1 j)).
Proof.
Admitted.

End BlockMatrix.

Notation "\mxblock_ ( i < m , j < n ) E" :=
  (mxblock (fun (i : 'I_m) (j : 'I_ n) => E)) (only parsing) : ring_scope.
Notation "\mxblock_ ( i , j < n ) E" :=
  (\mxblock_(i < n, j < n) E) (only parsing) : ring_scope.
Notation "\mxblock_ ( i , j ) E" := (\mxblock_(i < _, j < _) E) : ring_scope.
Notation "\mxrow_ ( j < m ) E" := (mxrow (fun (j : 'I_m) => E))
  (only parsing) : ring_scope.
Notation "\mxrow_ j E" := (\mxrow_(j < _) E) : ring_scope.
Notation "\mxcol_ ( i < m ) E" := (mxcol (fun (i : 'I_m) => E))
  (only parsing) : ring_scope.
Notation "\mxcol_ i E" := (\mxcol_(i < _) E) : ring_scope.

Lemma tr_mxblock {T : Type} {p q : nat} {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}
  (B_ : forall i j, 'M[T]_(p_ i, q_ j)) :
  (\mxblock_(i, j) B_ i j)^T = \mxblock_(i, j) (B_ j i)^T.
Proof.
Admitted.

Section SquareBlockMatrix.

Context {T : Type} {p : nat} {p_ : 'I_p -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma tr_mxrow n (B_ : forall j, 'M[T]_(n, p_ j)) :
  (\mxrow_j B_ j)^T = \mxcol_i (B_ i)^T.
Proof.
Admitted.

Lemma tr_mxcol n (B_ : forall i, 'M[T]_(p_ i, n)) :
  (\mxcol_i B_ i)^T = \mxrow_i (B_ i)^T.
Proof.
Admitted.

Lemma tr_submxblock (A : 'M[T]_sp) i j :
  (submxblock A i j)^T = (submxblock A^T j i).
Proof.
Admitted.

Lemma tr_submxrow n (A : 'M[T]_(n, sp)) j :
  (submxrow A j)^T = (submxcol A^T j).
Proof.
Admitted.

Lemma tr_submxcol n (A : 'M[T]_(sp, n)) i :
  (submxcol A i)^T = (submxrow A^T i).
Proof.
Admitted.

End SquareBlockMatrix.

Section BlockRowRecL.
Import tagnat.
Context {T : Type} {m : nat} {p_ : 'I_m.+1 -> nat}.
Notation sp := (\sum_i p_ i)%N.

Lemma mxsize_recl : (p_ ord0 + \sum_i p_ (lift ord0 i) = (\sum_i p_ i))%N.
Proof.
Admitted.

Lemma mxrow_recl n (B_ : forall j, 'M[T]_(n, p_ j)) :
  \mxrow_j B_ j = castmx (erefl, mxsize_recl)
    (row_mx (B_ 0) (\mxrow_j B_ (lift ord0 j))).
Proof.
Admitted.

End BlockRowRecL.

Lemma mxcol_recu {T : Type} {p : nat} {p_ : 'I_p.
Proof.
Admitted.

Section BlockMatrixRec.
Local Notation e := (mxsize_recl, mxsize_recl).
Local Notation l0 := (lift ord0).
Context {T : Type}.

Lemma mxblock_recu {p q : nat} {p_ : 'I_p.
Proof.
Admitted.

Lemma mxblock_recl {p q : nat} {p_ : 'I_p -> nat} {q_ : 'I_q.
Proof.
Admitted.

Lemma mxblock_recul {p q : nat} {p_ : 'I_p.
Proof.
Admitted.

Lemma mxrowEblock {q : nat} {q_ : 'I_q -> nat} m
    (R_ : forall j, 'M[T]_(m, q_ j)) :
  (\mxrow_j R_ j) =
  castmx (big_ord1 _ (fun=> m), erefl) (\mxblock_(i < 1, j < q) R_ j).
Proof.
Admitted.

Lemma mxcolEblock {p : nat} {p_ : 'I_p -> nat} n
    (C_ : forall i, 'M[T]_(p_ i, n)) :
  (\mxcol_i C_ i) =
  castmx (erefl, big_ord1 _ (fun=> n)) (\mxblock_(i < p, j < 1) C_ i).
Proof.
Admitted.

Lemma mxEmxrow m n (A : 'M[T]_(m, n)) :
  A = castmx (erefl, big_ord1 _ (fun=> n)) (\mxrow__ A).
Proof.
Admitted.

Lemma mxEmxcol m n (A : 'M[T]_(m, n)) :
  A = castmx (big_ord1 _ (fun=> m), erefl) (\mxcol__ A).
Proof.
Admitted.

Lemma mxEmxblock m n (A : 'M[T]_(m, n)) :
  A = castmx (big_ord1 _ (fun=> m), big_ord1 _ (fun=> n))
             (\mxblock_(i < 1, j < 1) A).
Proof.
Admitted.

End BlockMatrixRec.

Section BlockRowNmod.
Context {V : nmodType} {q : nat} {q_ : 'I_q -> nat}.
Notation sq := (\sum_i q_ i)%N.
Implicit Type (s : 'I_sq).

Lemma mxrowD m (R_ R'_ : forall j, 'M[V]_(m, q_ j)) :
  \mxrow_j (R_ j + R'_ j) = \mxrow_j (R_ j) + \mxrow_j (R'_ j).
Proof.
Admitted.

Lemma mxrow0 m : \mxrow_j (0 : 'M[V]_(m, q_ j)) = 0.
Proof.
Admitted.

Lemma mxrow_const m a : \mxrow_j (const_mx a : 'M[V]_(m, q_ j)) = const_mx a.
Proof.
Admitted.

Lemma mxrow_sum (J : finType) m
    (R_ : forall i j, 'M[V]_(m, q_ j)) (P : {pred J}) :
  \mxrow_j (\sum_(i | P i) R_ i j) = \sum_(i | P i) \mxrow_j (R_ i j).
Proof.
Admitted.

Lemma submxrowD m (B B' : 'M[V]_(m, sq)) j :
 submxrow (B + B') j = submxrow B j + submxrow B' j.
Proof.
Admitted.

Lemma submxrow0 m j : submxrow (0 : 'M[V]_(m, sq)) j = 0.
Proof.
Admitted.

Lemma submxrow_sum (J : finType) m
   (R_ : forall i, 'M[V]_(m, sq)) (P : {pred J}) j:
  submxrow (\sum_(i | P i) R_ i) j = \sum_(i | P i) submxrow (R_ i) j.
Proof.
Admitted.

End BlockRowNmod.

Section BlockRowZmod.
Context {V : zmodType} {q : nat} {q_ : 'I_q -> nat}.
Notation sq := (\sum_i q_ i)%N.
Implicit Type (s : 'I_sq).

Lemma mxrowN m (R_ : forall j, 'M[V]_(m, q_ j)) :
  \mxrow_j (- R_ j) = - \mxrow_j (R_ j).
Proof.
Admitted.

Lemma mxrowB m (R_ R'_ : forall j, 'M[V]_(m, q_ j)) :
  \mxrow_j (R_ j - R'_ j) = \mxrow_j (R_ j) - \mxrow_j (R'_ j).
Proof.
Admitted.

Lemma submxrowN m (B : 'M[V]_(m, sq)) j :
 submxrow (- B) j = - submxrow B j.
Proof.
Admitted.

Lemma submxrowB m (B B' : 'M[V]_(m, sq)) j :
 submxrow (B - B') j = submxrow B j - submxrow B' j.
Proof.
Admitted.

End BlockRowZmod.

Section BlockRowSemiRing.
Context {R : pzSemiRingType} {n : nat} {q_ : 'I_n -> nat}.
Notation sq := (\sum_i q_ i)%N.
Implicit Type (s : 'I_sq).

Lemma mul_mxrow m n' (A : 'M[R]_(m, n')) (R_ : forall j, 'M[R]_(n', q_ j)) :
  A *m \mxrow_j R_ j= \mxrow_j (A *m R_ j).
Proof.
Admitted.

Lemma mul_submxrow m n' (A : 'M[R]_(m, n')) (B : 'M[R]_(n', sq)) j :
  A *m submxrow B j= submxrow (A *m B) j.
Proof.
Admitted.

End BlockRowSemiRing.

Section BlockColNmod.
Context {V : nmodType} {n : nat} {p_ : 'I_n -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma mxcolD m (C_ C'_ : forall i, 'M[V]_(p_ i, m)) :
  \mxcol_i (C_ i + C'_ i) = \mxcol_i (C_ i) + \mxcol_i (C'_ i).
Proof.
Admitted.

Lemma mxcol0 m : \mxcol_i (0 : 'M[V]_(p_ i, m)) = 0.
Proof.
Admitted.

Lemma mxcol_const m a : \mxcol_j (const_mx a : 'M[V]_(p_ j, m)) = const_mx a.
Proof.
Admitted.

Lemma mxcol_sum
  (I : finType) m (C_ : forall j i, 'M[V]_(p_ i, m)) (P : {pred I}):
  \mxcol_i (\sum_(j | P j) C_ j i) = \sum_(j | P j) \mxcol_i (C_ j i).
Proof.
Admitted.

Lemma submxcolD m (B B' : 'M[V]_(sp, m)) i :
 submxcol (B + B') i = submxcol B i + submxcol B' i.
Proof.
Admitted.

Lemma submxcol0 m i : submxcol (0 : 'M[V]_(sp, m)) i = 0.
Proof.
Admitted.

Lemma submxcol_sum (I : finType) m
   (C_ : forall j, 'M[V]_(sp, m)) (P : {pred I}) i :
  submxcol (\sum_(j | P j) C_ j) i = \sum_(j | P j) submxcol (C_ j) i.
Proof.
Admitted.

End BlockColNmod.

Section BlockColZmod.
Context {V : zmodType} {n : nat} {p_ : 'I_n -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma mxcolN m (C_ : forall i, 'M[V]_(p_ i, m)) :
  \mxcol_i (- C_ i) = - \mxcol_i (C_ i).
Proof.
Admitted.

Lemma mxcolB m (C_ C'_ : forall i, 'M[V]_(p_ i, m)) :
  \mxcol_i (C_ i - C'_ i) = \mxcol_i (C_ i) - \mxcol_i (C'_ i).
Proof.
Admitted.

Lemma submxcolN m (B : 'M[V]_(sp, m)) i :
 submxcol (- B) i = - submxcol B i.
Proof.
Admitted.

Lemma submxcolB m (B B' : 'M[V]_(sp, m)) i :
 submxcol (B - B') i = submxcol B i - submxcol B' i.
Proof.
Admitted.

End BlockColZmod.

Section BlockColSemiRing.
Context {R : pzSemiRingType} {n : nat} {p_ : 'I_n -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma mxcol_mul n' m (C_ : forall i, 'M[R]_(p_ i, n')) (A : 'M[R]_(n', m)) :
  \mxcol_i C_ i *m A = \mxcol_i (C_ i *m A).
Proof.
Admitted.

Lemma submxcol_mul n' m (B : 'M[R]_(sp, n')) (A : 'M[R]_(n', m)) i :
  submxcol B i *m A = submxcol (B *m A) i.
Proof.
Admitted.

End BlockColSemiRing.

Section BlockMatrixNmod.
Context {V : nmodType} {m n : nat}.
Context {p_ : 'I_m -> nat} {q_ : 'I_n -> nat}.
Notation sp := (\sum_i p_ i)%N.
Notation sq := (\sum_i q_ i)%N.

Lemma mxblockD (B_ B'_ : forall i j, 'M[V]_(p_ i, q_ j)) :
  \mxblock_(i, j) (B_ i j + B'_ i j) =
  \mxblock_(i, j) (B_ i j) + \mxblock_(i, j) (B'_ i j).
Proof.
Admitted.

Lemma mxblock0 : \mxblock_(i, j) (0 : 'M[V]_(p_ i, q_ j)) = 0.
Proof.
Admitted.

Lemma mxblock_const a :
  \mxblock_(i, j) (const_mx a : 'M[V]_(p_ i, q_ j)) = const_mx a.
Proof.
Admitted.

Lemma mxblock_sum (I : finType)
    (B_ : forall k i j, 'M[V]_(p_ i, q_ j)) (P : {pred I}):
  \mxblock_(i, j) (\sum_(k | P k) B_ k i j) =
  \sum_(k | P k) \mxblock_(i, j) (B_ k i j).
Proof.
Admitted.

Lemma submxblockD (B B' : 'M[V]_(sp, sq)) i j :
 submxblock (B + B') i j = submxblock B i j + submxblock B' i j.
Proof.
Admitted.

Lemma submxblock0 i j : submxblock (0 : 'M[V]_(sp, sq)) i j = 0.
Proof.
Admitted.

Lemma submxblock_sum (I : finType)
   (B_ : forall k, 'M[V]_(sp, sq)) (P : {pred I}) i j :
  submxblock (\sum_(k | P k) B_ k) i j = \sum_(k | P k) submxblock (B_ k) i j.
Proof.
Admitted.

End BlockMatrixNmod.

Section BlockMatrixZmod.
Context {V : zmodType} {m n : nat}.
Context {p_ : 'I_m -> nat} {q_ : 'I_n -> nat}.
Notation sp := (\sum_i p_ i)%N.
Notation sq := (\sum_i q_ i)%N.

Lemma mxblockN (B_ : forall i j, 'M[V]_(p_ i, q_ j)) :
  \mxblock_(i, j) (- B_ i j) = - \mxblock_(i, j) (B_ i j).
Proof.
Admitted.

Lemma mxblockB (B_ B'_ : forall i j, 'M[V]_(p_ i, q_ j)) :
  \mxblock_(i, j) (B_ i j - B'_ i j) =
  \mxblock_(i, j) (B_ i j) - \mxblock_(i, j) (B'_ i j).
Proof.
Admitted.

Lemma submxblockN (B : 'M[V]_(sp, sq)) i j :
 submxblock (- B) i j = - submxblock B i j.
Proof.
Admitted.

Lemma submxblockB (B B' : 'M[V]_(sp, sq)) i j :
 submxblock (B - B') i j = submxblock B i j - submxblock B' i j.
Proof.
Admitted.

End BlockMatrixZmod.

Section BlockMatrixSemiRing.
Context {R : pzSemiRingType} {p q : nat} {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}.
Notation sp := (\sum_i p_ i)%N.
Notation sq := (\sum_i q_ i)%N.

Lemma mul_mxrow_mxcol m n
    (R_ : forall j, 'M[R]_(m, p_ j)) (C_ : forall i, 'M[R]_(p_ i, n)) :
  \mxrow_j R_ j *m \mxcol_i C_ i = \sum_i (R_ i *m C_ i).
Proof.
Admitted.

Lemma mul_mxcol_mxrow m
    (C_ : forall i, 'M[R]_(p_ i, m)) (R_ : forall j, 'M[R]_(m, q_ j)) :
  \mxcol_i C_ i*m \mxrow_j R_ j  = \mxblock_(i, j) (C_ i *m R_ j).
Proof.
Admitted.

Lemma mul_mxrow_mxblock m
    (R_ : forall i, 'M[R]_(m, p_ i)) (B_ : forall i j, 'M[R]_(p_ i, q_ j)) :
  \mxrow_i R_ i *m \mxblock_(i, j) B_ i j = \mxrow_j (\sum_i (R_ i *m B_ i j)).
Proof.
Admitted.

Lemma mul_mxblock_mxrow m
    (B_ : forall i j, 'M[R]_(q_ i, p_ j)) (C_ : forall i, 'M[R]_(p_ i, m)) :
  \mxblock_(i, j) B_ i j *m \mxcol_j C_ j = \mxcol_i (\sum_j (B_ i j *m C_ j)).
Proof.
Admitted.

End BlockMatrixSemiRing.

Lemma mul_mxblock {R : pzSemiRingType} {p q r : nat}
    {p_ : 'I_p -> nat} {q_ : 'I_q -> nat} {r_ : 'I_r -> nat}
    (A_ : forall i j, 'M[R]_(p_ i, q_ j)) (B_ : forall j k, 'M_(q_ j, r_ k)) :
  \mxblock_(i, j) A_ i j *m \mxblock_(j, k) B_ j k =
  \mxblock_(i, k) \sum_j (A_ i j *m B_ j k).
Proof.
Admitted.

Section SquareBlockMatrixNmod.
Import Order.TTheory tagnat.
Context {V : nmodType} {p : nat} {p_ : 'I_p -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma is_trig_mxblockP (B_ : forall i j, 'M[V]_(p_ i, p_ j)) :
  reflect [/\ forall (i j : 'I_p), (i < j)%N -> B_ i j = 0 &
              forall i, is_trig_mx (B_ i i)]
          (is_trig_mx (\mxblock_(i, j) B_ i j)).
Proof.
Admitted.

Lemma is_trig_mxblock (B_ : forall i j, 'M[V]_(p_ i, p_ j)) :
  is_trig_mx (\mxblock_(i, j) B_ i j) =
  ([forall i : 'I_p, forall j : 'I_p, (i < j)%N ==> (B_ i j == 0)] &&
   [forall i, is_trig_mx (B_ i i)]).
Proof.
Admitted.

Lemma is_diag_mxblockP (B_ : forall i j, 'M[V]_(p_ i, p_ j)) :
  reflect [/\ forall (i j : 'I_p), i != j -> B_ i j = 0 &
              forall i, is_diag_mx (B_ i i)]
          (is_diag_mx (\mxblock_(i, j) B_ i j)).
Proof.
Admitted.

Lemma is_diag_mxblock (B_ : forall i j, 'M[V]_(p_ i, p_ j)) :
  is_diag_mx (\mxblock_(i, j) B_ i j) =
  ([forall i : 'I_p, forall j : 'I_p, (i != j) ==> (B_ i j == 0)] &&
   [forall i, is_diag_mx (B_ i i)]).
Proof.
Admitted.

Definition mxdiag (B_ : forall i, 'M[V]_(p_ i)) : 'M[V]_(\sum_i p_ i) :=
  \mxblock_(j, k) if j == k then conform_mx 0 (B_ j) else 0.
Local Notation "\mxdiag_ i E" := (mxdiag (fun i => E)) : ring_scope.

Lemma submxblock_diag (B_  : forall i, 'M[V]_(p_ i)) i :
  submxblock (\mxdiag_i B_ i) i i = B_ i.
Proof.
Admitted.

Lemma eq_mxdiagP (B_ B'_ : forall i, 'M[V]_(p_ i)) :
  (forall i, B_ i = B'_ i) <-> (\mxdiag_i B_ i = \mxdiag_i B'_ i).
Proof.
Admitted.

Lemma eq_mxdiag (B_ B'_ : forall i, 'M[V]_(p_ i)) :
  (forall i, B_ i = B'_ i) -> (\mxdiag_i B_ i = \mxdiag_i B'_ i).
Proof.
Admitted.

Lemma mxdiagD (B_ B'_ : forall i, 'M[V]_(p_ i)) :
  \mxdiag_i (B_ i + B'_ i) = \mxdiag_i (B_ i) + \mxdiag_i (B'_ i).
Proof.
Admitted.

Lemma mxdiag_sum (I : finType) (B_ : forall k i, 'M[V]_(p_ i)) (P : {pred I}) :
  \mxdiag_i (\sum_(k | P k) B_ k i) = \sum_(k | P k) \mxdiag_i (B_ k i).
Proof.
Admitted.

Lemma tr_mxdiag (B_ : forall i, 'M[V]_(p_ i)) :
  (\mxdiag_i B_ i)^T = \mxdiag_i (B_ i)^T.
Proof.
Admitted.

Lemma row_mxdiag (B_ : forall i, 'M[V]_(p_ i)) k :
  let B'_ i := if sig1 k == i then conform_mx 0 (B_ i) else 0 in
  row k (\mxdiag_ i B_ i) = row (sig2 k) (\mxrow_i B'_ i).
Proof.
Admitted.

Lemma col_mxdiag (B_ : forall i, 'M[V]_(p_ i)) k :
  let B'_ i := if sig1 k == i then conform_mx 0 (B_ i) else 0 in
  col k (\mxdiag_ i B_ i) = col (sig2 k) (\mxcol_i B'_ i).
Proof.
Admitted.

End SquareBlockMatrixNmod.

Notation "\mxdiag_ ( i < n ) E" := (mxdiag (fun i : 'I_n => E))
  (only parsing) : ring_scope.
Notation "\mxdiag_ i E" := (\mxdiag_(i < _) E) : ring_scope.

Section SquareBlockMatrixZmod.
Import Order.TTheory tagnat.
Context {V : zmodType} {p : nat} {p_ : 'I_p -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma mxdiagN (B_ : forall i, 'M[V]_(p_ i)) :
  \mxdiag_i (- B_ i) = - \mxdiag_i (B_ i).
Proof.
Admitted.

Lemma mxdiagB (B_ B'_ : forall i, 'M[V]_(p_ i)) :
  \mxdiag_i (B_ i - B'_ i) = \mxdiag_i (B_ i) - \mxdiag_i (B'_ i).
Proof.
Admitted.

Lemma mxdiag0 : \mxdiag_i (0 : 'M[V]_(p_ i)) = 0.
Proof.
Admitted.

End SquareBlockMatrixZmod.

Lemma mxdiag_recl {V : nmodType} {m : nat} {p_ : 'I_m.
Proof.
Admitted.

Section SquareBlockMatrixSemiRing.
Import tagnat.
Context {R : pzSemiRingType} {p : nat} {p_ : 'I_p -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma mxtrace_mxblock (B_ : forall i j, 'M[R]_(p_ i, p_ j)) :
  \tr (\mxblock_(i, j) B_ i j) = \sum_i \tr (B_ i i).
Proof.
Admitted.

Lemma mxdiagZ a : \mxdiag_i (a%:M : 'M[R]_(p_ i)) = a%:M.
Proof.
Admitted.

Lemma diag_mxrow (B_ : forall j, 'rV[R]_(p_ j)) :
  diag_mx (\mxrow_j B_ j) = \mxdiag_j (diag_mx (B_ j)).
Proof.
Admitted.

Lemma mxtrace_mxdiag (B_ : forall i, 'M[R]_(p_ i)) :
  \tr (\mxdiag_i B_ i) = \sum_i \tr (B_ i).
Proof.
Admitted.

Lemma mul_mxdiag_mxcol m
    (D_ : forall i, 'M[R]_(p_ i)) (C_ : forall i, 'M[R]_(p_ i, m)):
  \mxdiag_i D_ i *m \mxcol_i C_ i = \mxcol_i (D_ i *m C_ i).
Proof.
Admitted.

End SquareBlockMatrixSemiRing.

Lemma mul_mxrow_mxdiag {R : pzSemiRingType} {p : nat} {p_ : 'I_p -> nat} m
    (R_ : forall i, 'M[R]_(m, p_ i)) (D_ : forall i, 'M[R]_(p_ i)) :
  \mxrow_i R_ i *m \mxdiag_i D_ i = \mxrow_i (R_ i *m D_ i).
Proof.
Admitted.

Lemma mul_mxblock_mxdiag {R : pzSemiRingType} {p q : nat}
  {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}
    (B_ : forall i j, 'M[R]_(p_ i, q_ j)) (D_ : forall j, 'M[R]_(q_ j)) :
  \mxblock_(i, j) B_ i j *m \mxdiag_j D_ j = \mxblock_(i, j) (B_ i j *m D_ j).
Proof.
Admitted.

Lemma mul_mxdiag_mxblock {R : pzSemiRingType} {p q : nat}
  {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}
    (D_ : forall j, 'M[R]_(p_ j)) (B_ : forall i j, 'M[R]_(p_ i, q_ j)):
  \mxdiag_j D_ j *m \mxblock_(i, j) B_ i j = \mxblock_(i, j) (D_ i *m B_ i j).
Proof.
Admitted.

Definition Vandermonde (R : pzRingType) (m n : nat) (a : 'rV[R]_n) :=
  \matrix_(i < m, j < n) a 0 j ^+ i.

Lemma det_Vandermonde (R : comPzRingType) (n : nat) (a : 'rV[R]_n) :
  \det (Vandermonde n a) = \prod_(i < n) \prod_(j < n | i < j) (a 0 j - a 0 i).
Proof.
Admitted.
