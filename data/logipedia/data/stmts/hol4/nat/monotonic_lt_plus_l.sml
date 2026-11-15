(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_lt_plus_l (catalog title "nat.monotonic_lt_plus_l"): adding
  a fixed natural number on the right preserves the strict natural-number
  order. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_monotonic_lt_plus_l =
  ``!(n : num) (x : num) (y : num).
      x < y ==> x + n < y + n``;
