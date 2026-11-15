(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_minus_comm (catalog title "nat.minus_minus_comm"): iterated
  truncated subtraction on the natural numbers is unchanged when the two
  subtrahends are exchanged. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_minus_minus_comm =
  ``!(a : num) (b : num) (c : num).
      (a - b) - c = (a - c) - b``;
