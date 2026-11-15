(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_to_eqb_true (catalog title "nat.eq_to_eqb_true"): equality of two
  natural numbers implies that their Boolean equality test is true. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_eq_to_eqb_true :
  forall n m : nat,
    n = m ->
    Nat.eqb n m = true.
Admitted.
