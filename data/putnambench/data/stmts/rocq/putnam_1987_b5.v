(* Statement-only formalization of PutnamBench artifact putnam_1987_b5:
   surjectivity of the real-part map induced by a complex 2n-by-n matrix
   under a condition on its nonzero left-kernel vectors. This file contains no proof. *)

From Stdlib Require Import Vectors.Fin Reals.

Open Scope R_scope.

Record putnam_1987_b5_complex : Type := putnam_1987_b5_Complex {
  putnam_1987_b5_real_part : R;
  putnam_1987_b5_imaginary_part : R
}.

Definition putnam_1987_b5_Czero : putnam_1987_b5_complex :=
  putnam_1987_b5_Complex 0 0.

Definition putnam_1987_b5_Cadd
    (z w : putnam_1987_b5_complex) : putnam_1987_b5_complex :=
  putnam_1987_b5_Complex
    (putnam_1987_b5_real_part z + putnam_1987_b5_real_part w)
    (putnam_1987_b5_imaginary_part z + putnam_1987_b5_imaginary_part w).

Definition putnam_1987_b5_Cmul
    (z w : putnam_1987_b5_complex) : putnam_1987_b5_complex :=
  putnam_1987_b5_Complex
    (putnam_1987_b5_real_part z * putnam_1987_b5_real_part w -
       putnam_1987_b5_imaginary_part z * putnam_1987_b5_imaginary_part w)
    (putnam_1987_b5_real_part z * putnam_1987_b5_imaginary_part w +
       putnam_1987_b5_imaginary_part z * putnam_1987_b5_real_part w).

Fixpoint putnam_1987_b5_fin_sum
    (n : nat) : (Fin.t n -> putnam_1987_b5_complex) ->
                putnam_1987_b5_complex :=
  match n as k return
      (Fin.t k -> putnam_1987_b5_complex) -> putnam_1987_b5_complex with
  | O => fun _ => putnam_1987_b5_Czero
  | S k =>
      fun f =>
        putnam_1987_b5_Cadd
          (f Fin.F1)
          (putnam_1987_b5_fin_sum k (fun i => f (Fin.FS i)))
  end.

Definition putnam_1987_b5_matrix (rows cols : nat) : Type :=
  Fin.t rows -> Fin.t cols -> putnam_1987_b5_complex.

Definition putnam_1987_b5_row_times_matrix
    {rows cols : nat}
    (z : Fin.t rows -> putnam_1987_b5_complex)
    (M : putnam_1987_b5_matrix rows cols)
    (j : Fin.t cols) : putnam_1987_b5_complex :=
  putnam_1987_b5_fin_sum rows
    (fun i => putnam_1987_b5_Cmul (z i) (M i j)).

Definition putnam_1987_b5_matrix_times_column
    {rows cols : nat}
    (M : putnam_1987_b5_matrix rows cols)
    (w : Fin.t cols -> putnam_1987_b5_complex)
    (i : Fin.t rows) : putnam_1987_b5_complex :=
  putnam_1987_b5_fin_sum cols
    (fun j => putnam_1987_b5_Cmul (M i j) (w j)).

Theorem putnam_1987_b5
    (n : nat)
    (npos : (0 < n)%nat)
    (M : putnam_1987_b5_matrix (2 * n) n)
    (hM :
      forall z : Fin.t (2 * n) -> putnam_1987_b5_complex,
        (forall j : Fin.t n,
          putnam_1987_b5_row_times_matrix z M j =
            putnam_1987_b5_Czero) ->
        (~ forall i : Fin.t (2 * n), z i = putnam_1987_b5_Czero) ->
        exists i : Fin.t (2 * n),
          putnam_1987_b5_imaginary_part (z i) <> 0) :
  forall r : Fin.t (2 * n) -> R,
    exists w : Fin.t n -> putnam_1987_b5_complex,
      forall i : Fin.t (2 * n),
        putnam_1987_b5_real_part
          (putnam_1987_b5_matrix_times_column M w i) = r i.
Admitted.
