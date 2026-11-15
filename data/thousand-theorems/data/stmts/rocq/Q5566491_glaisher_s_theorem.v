(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5566491
  (thousand-theorems__rocq__Q5566491), "Glaisher's theorem": for every
  natural number n and positive natural number m, the number of partitions of
  n into parts not divisible by m equals the number of partitions in which
  every part occurs fewer than m times. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat List Sorting.

Import ListNotations.

Fixpoint q5566491_sum_parts (parts : list nat) : nat :=
  match parts with
  | [] => 0
  | part :: rest => part + q5566491_sum_parts rest
  end.

(* A nondecreasing list of positive parts canonically represents an unordered
   partition; the empty list is the unique partition of zero. *)
Definition q5566491_partition (n : nat) (parts : list nat) : Prop :=
  Forall (fun part : nat => 0 < part) parts /\
  StronglySorted le parts /\
  q5566491_sum_parts parts = n.

Definition q5566491_divides (m part : nat) : Prop :=
  exists k : nat, part = m * k.

Definition q5566491_divisibility_restricted_partition
    (n m : nat) (parts : list nat) : Prop :=
  q5566491_partition n parts /\
  Forall (fun part : nat => ~ q5566491_divides m part) parts.

Definition q5566491_count_restricted_partition
    (n m : nat) (parts : list nat) : Prop :=
  q5566491_partition n parts /\
  forall part : nat,
    In part parts ->
    count_occ Nat.eq_dec parts part < m.

Definition q5566491_has_cardinality
    (P : list nat -> Prop) (card : nat) : Prop :=
  exists enumeration : list (list nat),
    NoDup enumeration /\
    length enumeration = card /\
    forall parts : list nat,
      In parts enumeration <-> P parts.

Theorem q5566491_glaisher_s_theorem :
  forall n m : nat,
    0 < m ->
    exists card : nat,
      q5566491_has_cardinality
        (q5566491_divisibility_restricted_partition n m) card /\
      q5566491_has_cardinality
        (q5566491_count_restricted_partition n m) card.
Admitted.
