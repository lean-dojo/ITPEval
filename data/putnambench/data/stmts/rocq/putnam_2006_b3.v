(* Statement-only formalization of PutnamBench corpus artifact putnam_2006_b3:
   the maximum number of unordered linear partitions of an n-point subset of
   the real plane is binomial(n, 2) + 1. This file contains no proof. *)

From Stdlib Require Import Reals Lists.List.

Open Scope R_scope.

Definition putnam_2006_b3_point := (R * R)%type.
Definition putnam_2006_b3_point_set := putnam_2006_b3_point -> Prop.

Definition putnam_2006_b3_same_set
    (A B : putnam_2006_b3_point_set) : Prop :=
  forall p : putnam_2006_b3_point, A p <-> B p.

Definition putnam_2006_b3_has_cardinality
    (S : putnam_2006_b3_point_set) (n : nat) : Prop :=
  exists points : list putnam_2006_b3_point,
    NoDup points /\
    length points = n /\
    forall p : putnam_2006_b3_point, In p points <-> S p.

Definition putnam_2006_b3_partition :=
  (putnam_2006_b3_point_set * putnam_2006_b3_point_set)%type.

Definition putnam_2006_b3_same_unordered_partition
    (P Q : putnam_2006_b3_partition) : Prop :=
  (putnam_2006_b3_same_set (fst P) (fst Q) /\
   putnam_2006_b3_same_set (snd P) (snd Q)) \/
  (putnam_2006_b3_same_set (fst P) (snd Q) /\
   putnam_2006_b3_same_set (snd P) (fst Q)).

Definition putnam_2006_b3_separated_by_a_line
    (A B : putnam_2006_b3_point_set) : Prop :=
  exists m b : R,
    ((forall p : putnam_2006_b3_point,
        A p -> snd p > m * fst p + b) /\
     (forall p : putnam_2006_b3_point,
        B p -> snd p < m * fst p + b)) \/
    ((forall p : putnam_2006_b3_point,
        B p -> snd p > m * fst p + b) /\
     (forall p : putnam_2006_b3_point,
        A p -> snd p < m * fst p + b)).

Definition putnam_2006_b3_linear_partition
    (S : putnam_2006_b3_point_set)
    (P : putnam_2006_b3_partition) : Prop :=
  ~ putnam_2006_b3_same_set (fst P) (snd P) /\
  (forall p : putnam_2006_b3_point,
    S p <-> fst P p \/ snd P p) /\
  (forall p : putnam_2006_b3_point,
    ~ (fst P p /\ snd P p)) /\
  putnam_2006_b3_separated_by_a_line (fst P) (snd P).

Fixpoint putnam_2006_b3_no_duplicate_partitions
    (partitions : list putnam_2006_b3_partition) : Prop :=
  match partitions with
  | nil => True
  | P :: rest =>
      (forall Q : putnam_2006_b3_partition,
        In Q rest ->
        ~ putnam_2006_b3_same_unordered_partition P Q) /\
      putnam_2006_b3_no_duplicate_partitions rest
  end.

Definition putnam_2006_b3_enumerates_linear_partitions
    (S : putnam_2006_b3_point_set)
    (partitions : list putnam_2006_b3_partition) : Prop :=
  putnam_2006_b3_no_duplicate_partitions partitions /\
  (forall P : putnam_2006_b3_partition,
    In P partitions ->
    putnam_2006_b3_linear_partition S P) /\
  (forall P : putnam_2006_b3_partition,
    putnam_2006_b3_linear_partition S P ->
    exists Q : putnam_2006_b3_partition,
      In Q partitions /\
      putnam_2006_b3_same_unordered_partition P Q).

Definition putnam_2006_b3_linear_partition_count
    (S : putnam_2006_b3_point_set) (k : nat) : Prop :=
  exists partitions : list putnam_2006_b3_partition,
    putnam_2006_b3_enumerates_linear_partitions S partitions /\
    length partitions = k.

Definition putnam_2006_b3_is_greatest
    (values : nat -> Prop) (maximum : nat) : Prop :=
  values maximum /\
  forall value : nat, values value -> (value <= maximum)%nat.

Fixpoint putnam_2006_b3_binomial (n k : nat) : nat :=
  match n, k with
  | _, O => 1%nat
  | O, S _ => 0%nat
  | S n', S k' =>
      (putnam_2006_b3_binomial n' k' +
       putnam_2006_b3_binomial n' (S k'))%nat
  end.

Definition putnam_2006_b3_solution (n : nat) : nat :=
  (putnam_2006_b3_binomial n 2 + 1)%nat.

Theorem putnam_2006_b3 :
  forall n : nat,
    (0 < n)%nat ->
    putnam_2006_b3_is_greatest
      (fun k : nat =>
        exists S : putnam_2006_b3_point_set,
          putnam_2006_b3_has_cardinality S n /\
          putnam_2006_b3_linear_partition_count S k)
      (putnam_2006_b3_solution n).
Admitted.
