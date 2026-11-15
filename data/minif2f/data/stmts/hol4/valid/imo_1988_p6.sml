(*
  Statement-only formalization of miniF2F valid artifact imo_1988_p6: a divisibility
  condition on two positive natural numbers whose resulting quotient is a perfect square.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val imo_1988_p6 =
  ``!a : num. !b : num.
      0 < a /\ 0 < b /\
      divides (a * b + 1) (a EXP 2 + b EXP 2)
      ==>
      ?x : num.
        x EXP 2 = (a EXP 2 + b EXP 2) DIV (a * b + 1)``;
