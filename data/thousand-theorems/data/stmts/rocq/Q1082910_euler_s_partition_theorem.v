(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1082910
  (thousand-theorems__rocq__Q1082910), "Euler's partition theorem": for every
  natural number, the number of partitions into odd positive parts equals the
  number of partitions into distinct positive parts. This file contains no
  proof.
*)

From Stdlib Require Import List Sorting.

Import ListNotations.

Fixpoint q1082910_sum_parts (parts : list nat) : nat :=
  match parts with
  | [] => 0
  | x :: xs => x + q1082910_sum_parts xs
  end.

(* A nondecreasing list of positive parts canonically represents an unordered
   partition; the empty list is the unique partition of zero. *)
Definition q1082910_partition (n : nat) (parts : list nat) : Prop :=
  Forall (fun x => 0 < x) parts /\
  StronglySorted le parts /\
  q1082910_sum_parts parts = n.

Definition q1082910_distinct_partition
    (n : nat) (parts : list nat) : Prop :=
  q1082910_partition n parts /\ NoDup parts.

Definition q1082910_odd_part (x : nat) : Prop :=
  exists k : nat, x = 2 * k + 1.

Definition q1082910_odd_partition
    (n : nat) (parts : list nat) : Prop :=
  q1082910_partition n parts /\
  Forall q1082910_odd_part parts.

Definition q1082910_has_cardinality
    (P : list nat -> Prop) (card : nat) : Prop :=
  exists enumeration : list (list nat),
    NoDup enumeration /\
    length enumeration = card /\
    forall parts : list nat,
      In parts enumeration <-> P parts.

Theorem q1082910_euler_partition_theorem :
  forall n : nat,
    exists card : nat,
      q1082910_has_cardinality
        (q1082910_odd_partition n) card /\
      q1082910_has_cardinality
        (q1082910_distinct_partition n) card.
Admitted.
