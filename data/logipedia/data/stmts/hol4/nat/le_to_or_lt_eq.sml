(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_to_or_lt_eq (catalog title "nat.le_to_or_lt_eq"): for natural
  numbers n and m, n less than or equal to m implies that n is less than m
  or n equals m. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_to_or_lt_eq =
  ``!(n : num) (m : num).
      n <= m ==> n < m \/ n = m``;
