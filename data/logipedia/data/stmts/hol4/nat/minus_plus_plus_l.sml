(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_plus_plus_l (catalog title "nat.minus_plus_plus_l"): adding the
  same natural number to both operands leaves truncated subtraction unchanged.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_minus_plus_plus_l =
  ``!(x : num) (y : num) (h : num).
      (x + h) - (y + h) = x - y``;
