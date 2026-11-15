(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_times_r (catalog title "nat.monotonic_le_times_r"):
  for every natural number n, multiplication by n on the left is monotone
  with respect to natural-number order. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_monotonic_le_times_r :
  forall n x y : nat,
    x <= y ->
    Nat.mul n x <= Nat.mul n y.
Admitted.
