(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.injn_Sn_n (catalog title "permutation.injn_Sn_n"): injectivity
  of a natural-number function on an initial segment through a successor
  implies injectivity on the preceding initial segment. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition injn (f : nat -> nat) (n : nat) : Prop :=
  forall i j : nat,
    i <= n ->
    j <= n ->
    f i = f j ->
    i = j.

Theorem injn_Sn_n :
  forall (f : nat -> nat) (n : nat),
    injn f (S n) ->
    injn f n.
Admitted.
