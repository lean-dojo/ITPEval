(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.distributive_times_minus (catalog title
  "nat.distributive_times_minus"): multiplication on natural numbers
  distributes over truncated subtraction. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_distributive_times_minus =
  ``!(a : num) (b : num) (c : num).
      a * (b - c) = a * b - a * c``;
