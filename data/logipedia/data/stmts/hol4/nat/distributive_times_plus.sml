(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.distributive_times_plus (catalog title
  "nat.distributive_times_plus"): multiplication on natural numbers
  distributes over addition. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_distributive_times_plus =
  ``!(a : num) (b : num) (c : num).
      a * (b + c) = a * b + a * c``;
