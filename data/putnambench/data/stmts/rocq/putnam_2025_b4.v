(* Statement-only formalization of PutnamBench corpus artifact putnam_2025_b4
   (putnambench__rocq__putnam_2025_b4): a bound relating the sum and number
   of nonzero entries of a square matrix of nonnegative integers with a
   prescribed zero region and unit-or-zero adjacent increments; this file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat.

Fixpoint putnam_2025_b4_row_sum
    (width row : nat) (A : nat -> nat -> nat) : nat :=
  match width with
  | O => O
  | S width' =>
      putnam_2025_b4_row_sum width' row A + A row width'
  end.

Fixpoint putnam_2025_b4_matrix_sum
    (height width : nat) (A : nat -> nat -> nat) : nat :=
  match height with
  | O => O
  | S height' =>
      putnam_2025_b4_matrix_sum height' width A +
      putnam_2025_b4_row_sum width height' A
  end.

Fixpoint putnam_2025_b4_row_nonzero_count
    (width row : nat) (A : nat -> nat -> nat) : nat :=
  match width with
  | O => O
  | S width' =>
      putnam_2025_b4_row_nonzero_count width' row A +
      if Nat.eqb (A row width') O then O else 1
  end.

Fixpoint putnam_2025_b4_nonzero_count
    (height width : nat) (A : nat -> nat -> nat) : nat :=
  match height with
  | O => O
  | S height' =>
      putnam_2025_b4_nonzero_count height' width A +
      putnam_2025_b4_row_nonzero_count width height' A
  end.

Theorem putnam_2025_b4
    (m : nat)
    (A : nat -> nat -> nat)
    (ha :
      forall i j : nat,
        (i < m + 2)%nat ->
        (j < m + 2)%nat ->
        (i + j <= m)%nat ->
        A i j = O)
    (hb :
      forall i j : nat,
        (i < m + 1)%nat ->
        (j < m + 2)%nat ->
        A (S i) j = A i j \/
        A (S i) j = A i j + 1)
    (hc :
      forall i j : nat,
        (i < m + 2)%nat ->
        (j < m + 1)%nat ->
        A i (S j) = A i j \/
        A i (S j) = A i j + 1)
    (total : nat)
    (h_total :
      total = putnam_2025_b4_matrix_sum (m + 2) (m + 2) A)
    (nonzero : nat)
    (h_nonzero :
      nonzero = putnam_2025_b4_nonzero_count (m + 2) (m + 2) A) :
  (3 * total <= (m + 4) * nonzero)%nat.
Admitted.
