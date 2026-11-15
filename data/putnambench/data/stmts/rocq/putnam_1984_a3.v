(* Statement-only formalization of PutnamBench artifact putnam_1984_a3:
   the punctured limit of a determinant of a parity-patterned real matrix;
   this file contains no proof. *)

From Stdlib Require Import Reals List Arith.

Import ListNotations.
Open Scope R_scope.

Fixpoint putnam_1984_a3_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_1984_a3_sum rest
  end.

Definition putnam_1984_a3_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_1984_a3_cofactor_sign (j : nat) : R :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_1984_a3_det
    (m : nat) (M : list (list R)) {struct m} : R :=
  match m with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_1984_a3_sum
            (map
              (fun j : nat =>
                putnam_1984_a3_cofactor_sign j *
                nth j row 0 *
                putnam_1984_a3_det k
                  (map (putnam_1984_a3_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_1984_a3_matrix
    (n : nat) (a b x : R) : list (list R) :=
  map
    (fun i : nat =>
      map
        (fun j : nat =>
          if Nat.eqb i j then x
          else if Nat.even (i + j) then a
          else b)
        (seq 0 (2 * n)))
    (seq 0 (2 * n)).

Definition putnam_1984_a3_punctured_limit
    (f : R -> R) (c l : R) : Prop :=
  forall eps : R,
    0 < eps ->
    exists delta : R,
      0 < delta /\
      forall x : R,
        0 < Rabs (x - c) < delta ->
        Rabs (f x - l) < eps.

Theorem putnam_1984_a3
    (n : nat)
    (a b : R)
    (npos : (0 < n)%nat)
    (aneb : a <> b) :
  putnam_1984_a3_punctured_limit
    (fun x : R =>
      putnam_1984_a3_det (2 * n)
        (putnam_1984_a3_matrix n a b x) /
      (x - a) ^ (2 * n - 2))
    a
    ((INR n) ^ 2 * (a ^ 2 - b ^ 2)).
Admitted.
