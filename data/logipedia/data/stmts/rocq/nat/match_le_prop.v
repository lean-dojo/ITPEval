(*
  Statement-only formalization of Logipedia corpus artifact nat.match_le_prop
  (catalog title "nat.match_le_prop"): elimination for natural numbers at or
  above a fixed lower bound. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_match_le_prop :
  forall (n : nat) (return_ : nat -> Prop),
    return_ n ->
    (forall m : nat, return_ (S m)) ->
    forall m : nat, n <= m -> return_ m.
Admitted.
