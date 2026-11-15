(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_plus_to_minus_r (catalog title "nat.le_plus_to_minus_r"): for
  natural numbers a, b, and c, a + b <= c implies a <= c - b, where
  subtraction is truncated natural-number subtraction. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_plus_to_minus_r =
  ``!(a : num) (b : num) (c : num).
      a + b <= c ==> a <= c - b``;
