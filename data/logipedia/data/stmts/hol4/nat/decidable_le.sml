(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.decidable_le (catalog title "nat.decidable_le"): for all natural
  numbers n and m, n is at most m or n is not at most m. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_decidable_le =
  ``!(n : num) (m : num). n <= m \/ ~(n <= m)``;
