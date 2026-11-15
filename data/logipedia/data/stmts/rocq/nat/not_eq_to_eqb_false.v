(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_eq_to_eqb_false (catalog title "nat.not_eq_to_eqb_false"):
  disequality of two natural numbers implies that their Boolean equality test
  is false. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_not_eq_to_eqb_false :
  forall n m : nat,
    n <> m ->
    Nat.eqb n m = false.
Admitted.
