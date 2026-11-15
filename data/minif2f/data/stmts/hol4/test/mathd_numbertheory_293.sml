(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_293:
  divisibility of the decimal expression 20 * 100 + 10 * n + 7 by 11 forces
  the natural-number digit n, bounded above by 9, to equal 5. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val mathd_numbertheory_293 =
  ``!n : num.
      n <= 9 /\
      divides 11 (20 * 100 + 10 * n + 7)
      ==>
      n = 5``;
