(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_le_times_r (catalog title "nat.monotonic_le_times_r"):
  left multiplication by any natural number is monotone with respect to the
  natural-number order. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_monotonic_le_times_r =
  ``!(n : num) (x : num) (y : num).
      x <= y ==> n * x <= n * y``;
