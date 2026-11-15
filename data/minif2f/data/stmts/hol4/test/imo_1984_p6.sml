(*
  Statement-only formalization of miniF2F test problem imo_1984_p6: the least of four ordered
  positive odd natural numbers is 1 when a*d = b*c and both a+d and b+c are powers of two.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val imo_1984_p6 =
  ``!a b c d k m : num.
      0 < a /\ 0 < b /\ 0 < c /\ 0 < d /\
      ODD a /\ ODD b /\ ODD c /\ ODD d /\
      a < b /\ b < c /\ c < d /\
      a * d = b * c /\
      a + d = 2 EXP k /\
      b + c = 2 EXP m
      ==>
      a = 1``;
