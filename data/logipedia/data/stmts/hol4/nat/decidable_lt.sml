(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.decidable_lt (catalog title "nat.decidable_lt"): for all natural
  numbers n and m, n is less than m or n is not less than m. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_decidable_lt =
  ``!(n : num) (m : num). n < m \/ ~(n < m)``;
