(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_430:
  three pairwise-distinct natural numbers between 1 and 9 satisfying the given
  addition, natural-number subtraction, and multiplication equations have sum 8.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_430 =
  ``!a b c : num.
      1 <= a /\ a <= 9 /\
      1 <= b /\ b <= 9 /\
      1 <= c /\ c <= 9 /\
      a <> b /\
      a <> c /\
      b <> c /\
      a + b = c /\
      10 * a + a - b = 2 * c /\
      c * b = 10 * a + a + a
      ==>
      a + b + c = 8``;
