(* Statement-only formalization of PutnamBench corpus artifact putnam_2009_a3:
   the determinants of the n by n real matrices with consecutive cosine
   entries converge to zero; this file contains no proof. *)

From Stdlib Require Import Reals List Arith.

Import ListNotations.
Open Scope R_scope.

Fixpoint putnam_2009_a3_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_2009_a3_sum rest
  end.

Definition putnam_2009_a3_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_2009_a3_cofactor_sign (j : nat) : R :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_2009_a3_det
    (n : nat) (M : list (list R)) {struct n} : R :=
  match n with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_2009_a3_sum
            (map
              (fun j : nat =>
                putnam_2009_a3_cofactor_sign j *
                nth j row 0 *
                putnam_2009_a3_det k
                  (map (putnam_2009_a3_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_2009_a3_matrix
    (n : nat) (A : nat -> nat -> R) : list (list R) :=
  map
    (fun i : nat =>
      map (fun j : nat => A i j) (seq 0 n))
    (seq 0 n).

Definition putnam_2009_a3_tends_to
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Theorem putnam_2009_a3
    (cos_matrix : nat -> nat -> nat -> R)
    (hM :
      forall n i j : nat,
        (i < n)%nat ->
        (j < n)%nat ->
        cos_matrix n i j =
          cos (INR ((1 + n * i + j)%nat))) :
  putnam_2009_a3_tends_to
    (fun n : nat =>
      putnam_2009_a3_det n
        (putnam_2009_a3_matrix n (cos_matrix n)))
    0.
Admitted.
