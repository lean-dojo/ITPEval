(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_to_not_zero (catalog title "nat.lt_to_not_zero"): a strict inequality
  between natural numbers implies that the greater number is nonzero. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_lt_to_not_zero =
  ``!(n : num) (m : num).
      n < m ==> ~(m = 0)``;
