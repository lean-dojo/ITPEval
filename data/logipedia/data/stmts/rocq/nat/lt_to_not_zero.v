(*
  Statement-only formalization of Logipedia corpus artifact
  nat.lt_to_not_zero (catalog title "nat.lt_to_not_zero"): strict inequality
  between natural numbers implies that the greater number is nonzero. This
  file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_lt_to_not_zero :
  forall n m : nat,
    Nat.lt n m ->
    m <> 0.
Admitted.
