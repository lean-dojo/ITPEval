(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_plus_to_minus_r (catalog title "nat.lt_plus_to_minus_r"): a strict
  natural-number inequality a + b < c implies a < c - b. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_lt_plus_to_minus_r =
  ``!(a : num) (b : num) (c : num).
      a + b < c ==> a < c - b``;
