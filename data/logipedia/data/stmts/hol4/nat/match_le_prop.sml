(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.match_le_prop (catalog title "nat.match_le_prop"): a predicate on the
  natural numbers that holds at n and at every successor holds at every
  natural number greater than or equal to n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_match_le_prop =
  ``!(n : num) (P : num -> bool).
      P n ==>
      (!m : num. P (SUC m)) ==>
      !m : num. n <= m ==> P m``;
