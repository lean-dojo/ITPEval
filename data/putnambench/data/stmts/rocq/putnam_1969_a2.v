(* Statement-only formalization of PutnamBench artifact putnam_1969_a2:
   the determinant of the finite real matrix with entries |i - j|.
   This file contains no proof. *)

From Stdlib Require Import Reals List Arith ZArith.

Import ListNotations.
Open Scope R_scope.

Fixpoint putnam_1969_a2_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_1969_a2_sum rest
  end.

Definition putnam_1969_a2_delete_nth
    {A : Type} (j : nat) (xs : list A) : list A :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_1969_a2_cofactor_sign (j : nat) : R :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_1969_a2_det
    (n : nat) (M : list (list R)) {struct n} : R :=
  match n with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_1969_a2_sum
            (map
              (fun j : nat =>
                putnam_1969_a2_cofactor_sign j *
                nth j row 0 *
                putnam_1969_a2_det k
                  (map (putnam_1969_a2_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_1969_a2_matrix (n : nat) : list (list R) :=
  map
    (fun i : nat =>
      map (fun j : nat => Rabs (INR i - INR j)) (seq 0 n))
    (seq 0 n).

Theorem putnam_1969_a2 :
  forall n : nat,
    (0 < n)%nat ->
    putnam_1969_a2_det n (putnam_1969_a2_matrix n) =
      powerRZ (-1) ((Z.of_nat n - 1)%Z) *
      IZR ((Z.of_nat n - 1)%Z) *
      powerRZ 2 ((Z.of_nat n - 2)%Z).
Admitted.
