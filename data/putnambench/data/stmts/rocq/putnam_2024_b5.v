(* Statement-only formalization of PutnamBench corpus artifact putnam_2024_b5:
   polynomial enumeration of two nondecreasing positive integer sequences
   sharing an upper bound, with nonnegative rational coefficients. This file
   contains no proof. *)

From Stdlib Require Import Lists.List Sorting.Sorted Arith.PeanoNat QArith ZArith.

Open Scope Q_scope.

Definition putnam_2024_b5_has_cardinality
    {A : Type} (P : A -> Prop) (cardinality : nat) : Prop :=
  exists enumeration : list A,
    NoDup enumeration /\
    length enumeration = cardinality /\
    forall value : A, In value enumeration <-> P value.

Definition putnam_2024_b5_qualifying_sequence
    (q : nat) (values : list nat) (z : nat) : Prop :=
  length values = q /\
  StronglySorted Nat.le values /\
  (1 <= hd 0 values)%nat /\
  (last values 0 <= z)%nat.

Record putnam_2024_b5_triple : Type := {
  putnam_2024_b5_x : list nat;
  putnam_2024_b5_y : list nat;
  putnam_2024_b5_z : nat
}.

Definition putnam_2024_b5_polynomial : Type := list Q.

Fixpoint putnam_2024_b5_polynomial_eval
    (coefficients : putnam_2024_b5_polynomial) (x : Q) : Q :=
  match coefficients with
  | nil => 0
  | coefficient :: remaining =>
      coefficient +
      x * putnam_2024_b5_polynomial_eval remaining x
  end.

Definition putnam_2024_b5_polynomial_coeff
    (coefficients : putnam_2024_b5_polynomial) (i : nat) : Q :=
  nth i coefficients 0.

Definition putnam_2024_b5_nat_to_Q (n : nat) : Q :=
  inject_Z (Z.of_nat n).

Theorem putnam_2024_b5 :
  forall
    (IsQualifyingSeq : nat -> list nat -> nat -> Prop)
    (k m : nat)
    (f : nat -> nat),
    (forall (q : nat) (values : list nat) (z : nat),
      (0 < q)%nat ->
      (IsQualifyingSeq q values z <->
       putnam_2024_b5_qualifying_sequence q values z)) ->
    (0 < k)%nat ->
    (0 < m)%nat ->
    (forall n : nat,
      putnam_2024_b5_has_cardinality
        (fun triple : putnam_2024_b5_triple =>
          IsQualifyingSeq
            k (putnam_2024_b5_x triple) (putnam_2024_b5_z triple) /\
          IsQualifyingSeq
            m (putnam_2024_b5_y triple) (putnam_2024_b5_z triple) /\
          (putnam_2024_b5_z triple <= n)%nat)
        (f n)) ->
    exists P : putnam_2024_b5_polynomial,
      (forall n : nat,
        (0 < n)%nat ->
        putnam_2024_b5_nat_to_Q (f n) ==
        putnam_2024_b5_polynomial_eval
          P (putnam_2024_b5_nat_to_Q n)) /\
      forall i : nat,
        (0 <= putnam_2024_b5_polynomial_coeff P i)%Q.
Admitted.
