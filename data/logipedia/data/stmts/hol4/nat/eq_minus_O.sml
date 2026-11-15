(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_minus_O (catalog title "nat.eq_minus_O"): subtracting a natural
  number from a less-than-or-equal natural number yields zero. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_eq_minus_O =
  ``!(n : num) (m : num).
      n <= m ==> n - m = 0``;
