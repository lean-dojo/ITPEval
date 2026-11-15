(*
  Statement-only formalization of "The Partition Theorem (Euler)" from Hundred Theorems item
  045. It states that partitions into distinct positive parts are in bijection with partitions
  into odd positive parts. This file contains no proof.
*)

From Stdlib Require Import List Sorting.

Import ListNotations.

Fixpoint sum_parts (parts : list nat) : nat :=
  match parts with
  | [] => 0
  | x :: xs => x + sum_parts xs
  end.

(* Positive parts in nondecreasing order canonically represent an unordered
   partition. In particular, the empty list is the partition of zero. *)
Definition canonical_partition (n : nat) (parts : list nat) : Prop :=
  Forall (fun x => 0 < x) parts /\
  StronglySorted le parts /\
  sum_parts parts = n.

Definition distinct_partition (n : nat) : Type :=
  { parts : list nat |
      canonical_partition n parts /\ NoDup parts }.

Definition odd_part (x : nat) : Prop :=
  exists k : nat, x = 2 * k + 1.

Definition odd_partition (n : nat) : Type :=
  { parts : list nat |
      canonical_partition n parts /\ Forall odd_part parts }.

Theorem Euler_partition_theorem :
  forall n : nat,
    exists (to_odd : distinct_partition n -> odd_partition n)
           (to_distinct : odd_partition n -> distinct_partition n),
      (forall p : distinct_partition n, to_distinct (to_odd p) = p) /\
      (forall p : odd_partition n, to_odd (to_distinct p) = p).
Admitted.
