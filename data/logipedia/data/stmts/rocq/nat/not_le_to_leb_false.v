(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_le_to_leb_false (catalog title "nat.not_le_to_leb_false"): if one
  natural number is not at most another, their Boolean less-than-or-equal
  test returns false. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_not_le_to_leb_false :
  forall n m : nat,
    ~ n <= m ->
    Nat.leb n m = false.
Admitted.
