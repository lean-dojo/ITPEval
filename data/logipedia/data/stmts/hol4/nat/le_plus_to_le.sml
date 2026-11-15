(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_plus_to_le (catalog title "nat.le_plus_to_le"): left addition
  reflects the natural-number order. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_plus_to_le =
  ``!(a : num) (n : num) (m : num).
      a + n <= a + m ==> n <= m``;
