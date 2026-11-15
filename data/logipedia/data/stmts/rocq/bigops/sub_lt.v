(*
  Statement-only formalization of Logipedia corpus artifact bigops.sub_lt
  (catalog title "bigops.sub_lt"): identity maps embed the indices selected
  below a natural-number bound into those selected below any larger bound.
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

Theorem bigops_sub_lt :
  forall (e : nat -> nat)
         (p : nat -> bool)
         (n m : nat),
    n <= m ->
    sub_hk (fun x : nat => x) (fun x : nat => x)
      n m p p e e.
Admitted.
