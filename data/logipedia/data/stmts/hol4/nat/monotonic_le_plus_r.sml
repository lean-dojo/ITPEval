(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_le_plus_r (catalog title "nat.monotonic_le_plus_r"): adding
  a fixed natural number on the left preserves the natural-number order.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_monotonic_le_plus_r =
  ``!(n : num) (x : num) (y : num).
      x <= y ==> n + x <= n + y``;
