(* Statement-only formalization of PutnamBench corpus artifact putnam_2010_b6:
   equality of ordinary and entrywise positive powers of a real square matrix
   follows for every exponent from the first n+1 cases. This file contains no
   proof. *)

From Stdlib Require Import Lists.List Vectors.Fin Reals Arith.PeanoNat.

Import ListNotations.
Open Scope R_scope.

Definition putnam_2010_b6_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> R.

Definition putnam_2010_b6_matrix_eq
    {n : nat}
    (A B : putnam_2010_b6_matrix n) : Prop :=
  forall i j : Fin.t n, A i j = B i j.

Fixpoint putnam_2010_b6_indices (n : nat) : list (Fin.t n) :=
  match n with
  | O => []
  | S k => Fin.F1 :: map Fin.FS (putnam_2010_b6_indices k)
  end.

Fixpoint putnam_2010_b6_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_2010_b6_sum rest
  end.

Definition putnam_2010_b6_mul
    {n : nat}
    (A B : putnam_2010_b6_matrix n) :
    putnam_2010_b6_matrix n :=
  fun i j =>
    putnam_2010_b6_sum
      (map
        (fun k => A i k * B k j)
        (putnam_2010_b6_indices n)).

Definition putnam_2010_b6_identity
    (n : nat) : putnam_2010_b6_matrix n :=
  fun i j =>
    if Fin.eq_dec i j then 1 else 0.

Fixpoint putnam_2010_b6_matrix_power
    {n : nat}
    (A : putnam_2010_b6_matrix n)
    (k : nat) : putnam_2010_b6_matrix n :=
  match k with
  | O => putnam_2010_b6_identity n
  | S l =>
      putnam_2010_b6_mul A
        (putnam_2010_b6_matrix_power A l)
  end.

Definition putnam_2010_b6_entrywise_power
    {n : nat}
    (A : putnam_2010_b6_matrix n)
    (k : nat) : putnam_2010_b6_matrix n :=
  fun i j => (A i j) ^ k.

Theorem putnam_2010_b6
    (n : nat)
    (npos : (1 <= n)%nat)
    (A : putnam_2010_b6_matrix n)
    (Apow : nat -> putnam_2010_b6_matrix n)
    (hApow :
      forall k : nat,
        (0 < k)%nat ->
        putnam_2010_b6_matrix_eq
          (Apow k)
          (putnam_2010_b6_entrywise_power A k)) :
  (forall k : nat,
    (1 <= k <= n + 1)%nat ->
    putnam_2010_b6_matrix_eq
      (putnam_2010_b6_matrix_power A k)
      (Apow k)) ->
  forall k : nat,
    (1 <= k)%nat ->
    putnam_2010_b6_matrix_eq
      (putnam_2010_b6_matrix_power A k)
      (Apow k).
Admitted.
