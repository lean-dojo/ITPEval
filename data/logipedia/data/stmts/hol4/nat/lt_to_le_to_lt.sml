(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_to_le_to_lt (catalog title "nat.lt_to_le_to_lt"): for natural
  numbers n, m, and p, if n is less than m and m is less than or equal to p,
  then n is less than p. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_lt_to_le_to_lt =
  ``!(n : num) (m : num) (p : num).
      n < m ==> m <= p ==> n < p``;
