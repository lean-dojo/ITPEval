(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_a2:
  the integer recurrence a 0 = 1, a 1 = 2, and
  a n = 4 * a (n - 1) - a (n - 2) has 181 as an odd prime divisor of
  a 2015. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val putnam_2015_a2 =
  ``!a : num -> int.
      a 0 = 1 /\
      a 1 = 2 /\
      (!n : num.
         2 <= n
         ==>
         a n = 4 * a (n - 1) - a (n - 2))
      ==>
      ODD 181 /\
      prime 181 /\
      (181 : int) int_divides a 2015``;
