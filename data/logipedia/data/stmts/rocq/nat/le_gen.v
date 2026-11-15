(*
  Statement-only formalization of Logipedia corpus artifact nat.le_gen
  (catalog title "nat.le_gen"): a predicate holding for every natural number
  at most n holds at n itself. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_gen :
  forall (P : nat -> Prop) (n : nat),
    (forall i : nat, i <= n -> P i) ->
    P n.
Admitted.
