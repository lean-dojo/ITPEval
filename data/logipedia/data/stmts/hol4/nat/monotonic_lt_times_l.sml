(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_lt_times_l (catalog title "nat.monotonic_lt_times_l"):
  multiplication on the right by a positive natural number preserves the
  strict natural-number order. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_monotonic_lt_times_l =
  ``!(c : num) (x : num) (y : num).
      0 < c ==>
      x < y ==>
      x * c < y * c``;
