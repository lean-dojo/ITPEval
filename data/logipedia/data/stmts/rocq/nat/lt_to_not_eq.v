(*
  Statement-only formalization of Logipedia corpus artifact
  nat.lt_to_not_eq (catalog title "nat.lt_to_not_eq"): strict inequality
  between natural numbers implies that they are not equal. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_lt_to_not_eq :
  forall n m : nat,
    Nat.lt n m ->
    n <> m.
Admitted.
