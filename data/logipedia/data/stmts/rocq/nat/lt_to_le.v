(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_to_le
  (catalog title "nat.lt_to_le"): for all natural numbers x and y, strict
  inequality x < y implies non-strict inequality x <= y. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_lt_to_le :
  forall x y : nat,
    x < y ->
    x <= y.
Admitted.
