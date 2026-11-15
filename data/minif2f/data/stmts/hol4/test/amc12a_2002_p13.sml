(*
  Statement-only formalization of miniF2F test problem amc12a_2002_p13: distinct positive
  real solutions of |x - 1/x| = 1 have sum sqrt 5. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val amc12a_2002_p13 =
  ``!a b : real.
      0 < a /\ 0 < b /\
      ~(a = b) /\
      abs (a - 1 / a) = 1 /\
      abs (b - 1 / b) = 1
      ==>
      a + b = sqrt 5``;
