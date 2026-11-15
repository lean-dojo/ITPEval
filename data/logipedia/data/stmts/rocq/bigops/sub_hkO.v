(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.sub_hkO (catalog title "bigops.sub_hkO"):
  an empty source bound makes the sub-indexing condition between selected
  natural-number indices hold vacuously. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Bool.Bool.

Definition sub_hk
    (h k : nat -> nat) (n1 n2 : nat)
    (p1 p2 : nat -> bool) (f1 f2 : nat -> nat) : Prop :=
  forall i : nat,
    i < n1 ->
    p1 i = true ->
    (h i < n2 /\ p2 (h i) = true) /\ k (h i) = i.

Theorem bigops_sub_hkO :
  forall (h k : nat -> nat)
         (n1 n2 : nat)
         (p1 p2 : nat -> bool)
         (f1 f2 : nat -> nat),
    n1 = 0 ->
    sub_hk h k n1 n2 p1 p2 f1 f2.
Admitted.
