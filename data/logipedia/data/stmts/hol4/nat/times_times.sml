(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.times_times (catalog title "nat.times_times"): for all natural numbers,
  swapping the first two factors in a nested product leaves the result
  unchanged. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_times_times =
  ``!(x : num) (y : num) (z : num).
      x * (y * z) = y * (x * z)``;
