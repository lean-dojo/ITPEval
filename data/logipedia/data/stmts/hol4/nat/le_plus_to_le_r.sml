(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_plus_to_le_r (catalog title "nat.le_plus_to_le_r"): right addition
  by a common natural number reflects the natural-number order. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_plus_to_le_r =
  ``!(a : num) (n : num) (m : num).
      n + a <= m + a ==> n <= m``;
