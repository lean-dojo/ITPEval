(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eqb_true_to_eq (catalog title "nat.eqb_true_to_eq"): if the Boolean
  equality test of two natural numbers is true, then the natural numbers are
  equal. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_eqb_true_to_eq :
  forall n m : nat,
    Nat.eqb n m = true ->
    n = m.
Admitted.
