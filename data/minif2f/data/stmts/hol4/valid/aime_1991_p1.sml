(*
  Statement-only formalization of miniF2F valid problem aime_1991_p1: a natural-number
  Diophantine system determining the sum of two squares. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val aime_1991_p1 =
  ``!x y : num.
      0 < x /\ 0 < y /\
      x * y + (x + y) = 71 /\
      x EXP 2 * y + x * y EXP 2 = 880
      ==>
      x EXP 2 + y EXP 2 = 146``;
