(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_le_plus_l (catalog title "nat.monotonic_le_plus_l"): adding
  a fixed natural number on the right preserves the natural-number order.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_monotonic_le_plus_l =
  ``!(m : num) (x : num) (y : num).
      x <= y ==> x + m <= y + m``;
