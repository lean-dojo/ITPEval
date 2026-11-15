(*
  Statement-only formalization of Logipedia corpus artifact
  nat.minus_le_minus_minus_comm (catalog title
  "nat.minus_le_minus_minus_comm"): if one natural number is at most another,
  subtracting their difference from a third number equals subtracting the
  larger number from the sum of the third and smaller numbers. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_minus_le_minus_minus_comm :
  forall b c a : nat,
    Nat.le c b ->
    Nat.sub a (Nat.sub b c) = Nat.sub (Nat.add a c) b.
Admitted.
