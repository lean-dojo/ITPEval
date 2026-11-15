(*
  Statement-only formalization of miniF2F test problem amc12a_2008_p25: coupled real
  recurrences with values fixed at index 100 and a claimed sum at index 1. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val amc12a_2008_p25 =
  ``!a b : num -> real.
      (!n. a (n + 1) = sqrt 3 * a n - b n) /\
      (!n. b (n + 1) = sqrt 3 * b n + a n) /\
      a 100 = 2 /\
      b 100 = 4
      ==>
      a 1 + b 1 = 1 / (2 pow 98)``;
