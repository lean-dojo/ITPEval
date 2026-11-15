(*
  Statement-only formalization of the Logipedia corpus artifact nat.le_gen
  (catalog title "nat.le_gen"): if a predicate holds for every natural number
  at most n, then it holds at n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_gen =
  ``!(P : num -> bool) (n : num).
      (!i : num. i <= n ==> P i)
      ==>
      P n``;
