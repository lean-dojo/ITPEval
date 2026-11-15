(* Statement-only formalization of PutnamBench corpus artifact putnam_2025_a5
   (putnambench__rocq__putnam_2025_a5): the sign sequences maximizing the
   number of permutations with prescribed adjacent rises and falls are exactly
   the two alternating sign patterns. This file contains no proof. *)

From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.

Import ListNotations.

Fixpoint putnam_2025_a5_insert_everywhere
    (x : nat) (values : list nat) : list (list nat) :=
  match values with
  | [] => [[x]]
  | y :: ys =>
      (x :: y :: ys) ::
      map (cons y) (putnam_2025_a5_insert_everywhere x ys)
  end.

Fixpoint putnam_2025_a5_permutations
    (values : list nat) : list (list nat) :=
  match values with
  | [] => [[]]
  | x :: xs =>
      flat_map (putnam_2025_a5_insert_everywhere x)
        (putnam_2025_a5_permutations xs)
  end.

Definition putnam_2025_a5_satisfies
    (n : nat) (s : nat -> Z) (permutation : list nat) : bool :=
  forallb
    (fun i : nat =>
      Z.ltb 0
        (s i *
         (Z.of_nat (nth (S i) permutation 0) -
          Z.of_nat (nth i permutation 0))))
    (seq 0 n).

Definition putnam_2025_a5_f
    (n : nat) (s : nat -> Z) : nat :=
  length
    (filter
      (putnam_2025_a5_satisfies n s)
      (putnam_2025_a5_permutations (seq 0 (S n)))).

Definition putnam_2025_a5_sign_sequence
    (n : nat) (s : nat -> Z) : Prop :=
  forall i : nat,
    (i < n)%nat ->
    s i = 1%Z \/ s i = (-1)%Z.

Definition putnam_2025_a5_solution
    (n : nat) (s : nat -> Z) : Prop :=
  (forall i : nat,
      (i < n)%nat ->
      s i = Z.pow (-1) (Z.of_nat (S i))) \/
  (forall i : nat,
      (i < n)%nat ->
      s i = Z.pow (-1) (Z.of_nat i)).

Theorem putnam_2025_a5 :
  forall (n : nat) (s : nat -> Z),
    (1 <= n)%nat ->
    putnam_2025_a5_sign_sequence n s ->
    ((forall t : nat -> Z,
        putnam_2025_a5_sign_sequence n t ->
        (putnam_2025_a5_f n t <= putnam_2025_a5_f n s)%nat) <->
     putnam_2025_a5_solution n s).
Admitted.
