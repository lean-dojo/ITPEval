(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_le_minus_r (catalog title "nat.monotonic_le_minus_r"):
  truncated subtraction on natural numbers is order-reversing in its right
  argument. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_monotonic_le_minus_r =
  ``!(p : num) (q : num) (n : num).
      q <= p ==> (n - p) <= (n - q)``;
