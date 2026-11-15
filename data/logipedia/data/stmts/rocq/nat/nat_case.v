(*
  Statement-only formalization of Logipedia corpus artifact nat.nat_case
  (catalog title "nat.nat_case"): case analysis for a predicate on a natural
  number using its zero and successor alternatives. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_nat_case :
  forall (n : nat) (P : nat -> Prop),
    (n = O -> P O) ->
    (forall m : nat, n = S m -> P (S m)) ->
    P n.
Admitted.
