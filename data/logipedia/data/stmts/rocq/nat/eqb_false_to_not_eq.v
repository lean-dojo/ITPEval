(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eqb_false_to_not_eq (catalog title "nat.eqb_false_to_not_eq"): a false
  Boolean equality test for two natural numbers implies their disequality.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_eqb_false_to_not_eq :
  forall n m : nat,
    Nat.eqb n m = false ->
    n <> m.
Admitted.
