(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.sub0_to_false (catalog title "bigops.sub0_to_false"):
  a reverse sub-indexing into an empty natural-number range forces the source
  Boolean predicate to be false below its bound. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Bool.Bool.

Definition sub_hk
    (h k : nat -> nat) (n1 n2 : nat)
    (p1 p2 : nat -> bool) (f1 f2 : nat -> nat) : Prop :=
  forall i : nat,
    i < n1 ->
    p1 i = true ->
    (h i < n2 /\ p2 (h i) = true) /\ k (h i) = i.

Theorem bigops_sub0_to_false :
  forall (h k : nat -> nat)
         (n1 n2 : nat)
         (p1 p2 : nat -> bool)
         (f1 f2 : nat -> nat),
    n1 = 0 ->
    sub_hk h k n2 n1 p2 p1 f2 f1 ->
    forall i : nat,
      i < n2 ->
      p2 i = false.
Admitted.
