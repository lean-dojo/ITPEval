(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_b5:
  consecutive heights of base-two natural-number tetration are congruent
  modulo every natural number n at least two. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val putnam_1997_b5 =
  ``!n : num. !tetration : num -> num -> num.
      2 <= n /\
      (!a : num. tetration a 0 = 1) /\
      (!a m : num.
         tetration a (m + 1) = a EXP (tetration a m))
      ==>
      tetration 2 n MOD n = tetration 2 (n - 1) MOD n``;
