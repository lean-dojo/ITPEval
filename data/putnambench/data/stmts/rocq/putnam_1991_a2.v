(* Statement-only formalization of PutnamBench corpus artifact putnam_1991_a2:
   nonexistence of distinct real square matrices satisfying two cubic
   identities whose sum of squares is invertible. This file contains no proof. *)

From Stdlib Require Import Lists.List Vectors.Fin Reals.

Import ListNotations.
Open Scope R_scope.

Definition putnam_1991_a2_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> R.

Definition putnam_1991_a2_matrix_eq
    {n : nat}
    (A B : putnam_1991_a2_matrix n) : Prop :=
  forall i j, A i j = B i j.

Fixpoint putnam_1991_a2_indices (n : nat) : list (Fin.t n) :=
  match n with
  | O => []
  | S k => Fin.F1 :: map Fin.FS (putnam_1991_a2_indices k)
  end.

Fixpoint putnam_1991_a2_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_1991_a2_sum rest
  end.

Definition putnam_1991_a2_mul
    {n : nat}
    (A B : putnam_1991_a2_matrix n) :
    putnam_1991_a2_matrix n :=
  fun i j =>
    putnam_1991_a2_sum
      (map
        (fun k => A i k * B k j)
        (putnam_1991_a2_indices n)).

Definition putnam_1991_a2_add
    {n : nat}
    (A B : putnam_1991_a2_matrix n) :
    putnam_1991_a2_matrix n :=
  fun i j => A i j + B i j.

Definition putnam_1991_a2_identity
    (n : nat) : putnam_1991_a2_matrix n :=
  fun i j =>
    if Fin.eq_dec i j then 1 else 0.

Definition putnam_1991_a2_invertible
    {n : nat} (A : putnam_1991_a2_matrix n) : Prop :=
  exists B : putnam_1991_a2_matrix n,
    putnam_1991_a2_matrix_eq
      (putnam_1991_a2_mul A B)
      (putnam_1991_a2_identity n) /\
    putnam_1991_a2_matrix_eq
      (putnam_1991_a2_mul B A)
      (putnam_1991_a2_identity n).

Definition putnam_1991_a2_solution : Prop := False.

Theorem putnam_1991_a2
    (n : nat)
    (hn : (1 <= n)%nat) :
  putnam_1991_a2_solution <->
  exists A B : putnam_1991_a2_matrix n,
    ~ putnam_1991_a2_matrix_eq A B /\
    putnam_1991_a2_matrix_eq
      (putnam_1991_a2_mul (putnam_1991_a2_mul A A) A)
      (putnam_1991_a2_mul (putnam_1991_a2_mul B B) B) /\
    putnam_1991_a2_matrix_eq
      (putnam_1991_a2_mul (putnam_1991_a2_mul A A) B)
      (putnam_1991_a2_mul (putnam_1991_a2_mul B B) A) /\
    putnam_1991_a2_invertible
      (putnam_1991_a2_add
        (putnam_1991_a2_mul A A)
        (putnam_1991_a2_mul B B)).
Admitted.
