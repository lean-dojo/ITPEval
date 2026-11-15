(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_to_lt_to_lt (catalog title "nat.le_to_lt_to_lt"): for natural
  numbers n, m, and p, if n is less than or equal to m and m is strictly
  less than p, then n is strictly less than p. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_to_lt_to_lt =
  ``!(n : num) (m : num) (p : num).
      n <= m ==> m < p ==> n < p``;
