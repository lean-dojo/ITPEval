(*
  Statement-only formalization of PutnamBench artifact putnam_1970_a1:
  the power series of exp (a*x) * cos (b*x), for positive real a and b, has
  either no zero coefficients or infinitely many. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory seqTheory transcTheory;

val putnam_1970_a1 =
  ``!a b : real. !p : num -> real.
      0 < a /\ 0 < b /\
      (?c : real.
         0 < c /\
         !x : real.
           abs x < c
           ==>
           (\n : num. p n * x pow n) sums
             (exp (a * x) * cos (b * x)))
      ==>
      {n : num | p n = 0} = EMPTY \/
      INFINITE {n : num | p n = 0}``;
