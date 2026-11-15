(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_427:
  if a is the sum of the natural divisors of 500, then the sum of the prime
  natural divisors of a is 25. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val mathd_numbertheory_427 =
  ``!a : num.
      a = SIGMA (\k : num. k) {k : num | divides k 500}
      ==>
      SIGMA (\k : num. k) {k : num | prime k /\ divides k a} = 25``;
