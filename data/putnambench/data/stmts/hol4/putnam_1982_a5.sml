(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1982_a5:
  a lower bound for the positive deficit of a sum of two rational numbers
  formed from positive integers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val putnam_1982_a5 =
  ``!a b c d : num.
      0 < a /\ 0 < b /\ 0 < c /\ 0 < d /\
      a + c <= 1982 /\
      (&a : real) / (&b : real) + (&c : real) / (&d : real) < 1
      ==>
      1 - (&a : real) / (&b : real) - (&c : real) / (&d : real) >
        1 / ((1983 : real) pow 3)``;
