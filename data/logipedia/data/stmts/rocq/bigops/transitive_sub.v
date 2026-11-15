(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.transitive_sub (catalog title "bigops.transitive_sub"):
  transitivity of selected finite-range index embeddings under composition.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Bool.Bool.

Definition sub_hk
    (h k : nat -> nat) (n1 n2 : nat)
    (p1 p2 : nat -> bool) (f1 f2 : nat -> nat) : Prop :=
  forall i : nat,
    i < n1 ->
    p1 i = true ->
    (h i < n2 /\ p2 (h i) = true) /\ k (h i) = i.

Theorem bigops_transitive_sub :
  forall (h1 k1 h2 k2 : nat -> nat)
         (n1 n2 n3 : nat)
         (p1 p2 p3 : nat -> bool)
         (f1 f2 f3 : nat -> nat),
    sub_hk h1 k1 n1 n2 p1 p2 f1 f2 ->
    sub_hk h2 k2 n2 n3 p2 p3 f2 f3 ->
    sub_hk
      (fun x : nat => h2 (h1 x))
      (fun x : nat => k1 (k2 x))
      n1 n3 p1 p3 f1 f3.
Admitted.
