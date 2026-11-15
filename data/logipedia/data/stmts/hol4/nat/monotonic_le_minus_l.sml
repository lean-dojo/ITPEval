(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_le_minus_l (catalog title "nat.monotonic_le_minus_l"):
  truncated subtraction of the same natural number from two ordered natural
  numbers preserves their order. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_monotonic_le_minus_l =
  ``!(p : num) (q : num) (n : num).
      q <= p ==> q - n <= p - n``;
