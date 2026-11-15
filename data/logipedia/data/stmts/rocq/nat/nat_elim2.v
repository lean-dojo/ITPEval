(*
  Statement-only formalization of Logipedia corpus artifact nat.nat_elim2
  (catalog title "nat.nat_elim2"): two-dimensional induction over pairs of
  natural numbers from the zero-row, positive zero-column, and simultaneous
  successor cases. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_nat_elim2 :
  forall R : nat -> nat -> Prop,
    (forall n : nat, R O n) ->
    (forall n : nat, R (S n) O) ->
    (forall n m : nat, R n m -> R (S n) (S m)) ->
    forall n m : nat, R n m.
Abort.
