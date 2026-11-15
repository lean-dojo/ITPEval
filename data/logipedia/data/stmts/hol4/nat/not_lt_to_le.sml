(*
  Statement-only formalization of Logipedia corpus artifact nat.not_lt_to_le
  (catalog title "nat.not_lt_to_le"): for natural numbers n and m, if n is
  not strictly less than m, then m is less than or equal to n. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_not_lt_to_le =
  ``!(n : num) (m : num).
      ~(n < m) ==> m <= n``;
