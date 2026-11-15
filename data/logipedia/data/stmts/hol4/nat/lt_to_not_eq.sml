(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_to_not_eq (catalog title "nat.lt_to_not_eq"): a strict inequality
  between natural numbers implies that the numbers are unequal. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_lt_to_not_eq =
  ``!(n : num) (m : num).
      n < m ==> ~(n = m)``;
