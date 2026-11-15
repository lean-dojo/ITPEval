(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_a3:
  the classification of positive natural-number solutions to a coprime
  exponential Diophantine equation. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val putnam_1992_a3 =
  ``!m : num.
      0 < m
      ==>
      !n x y : num.
        ((?r : num.
            x = 2 EXP r /\
            y = 2 EXP r /\
            n = 2 * r + 1 /\
            m = 2 * r) <=>
         0 < n /\
         0 < x /\
         0 < y /\
         coprime n m /\
         (x EXP 2 + y EXP 2) EXP m = (x * y) EXP n)``;
