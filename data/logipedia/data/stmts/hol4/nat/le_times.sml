(*
  Statement-only formalization of the Logipedia corpus artifact nat.le_times
  (catalog title "nat.le_times"): multiplication on the natural numbers is
  monotone in both arguments. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_times =
  ``!(n1 : num) (n2 : num) (m1 : num) (m2 : num).
      n1 <= n2 ==>
      m1 <= m2 ==>
      n1 * m1 <= n2 * m2``;
