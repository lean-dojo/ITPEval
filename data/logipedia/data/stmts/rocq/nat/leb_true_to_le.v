(*
  Statement-only formalization of Logipedia corpus artifact
  nat.leb_true_to_le (catalog title "nat.leb_true_to_le"): if the Boolean
  less-than-or-equal test of two natural numbers returns true, then the first
  natural number is at most the second. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_leb_true_to_le :
  forall n m : nat,
    Nat.leb n m = true ->
    n <= m.
Admitted.
