(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_a3:
  coefficients of the local real power-series expansion of
  1 / (1 - 2*x - x^2) have each adjacent sum of squares occur as another
  coefficient. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory;

val putnam_1999_a3 =
  ``!a : num -> real.
      (?epsilon : real.
         0 < epsilon /\
         !x : real.
           abs x < epsilon
           ==>
           (\k : num. a k * x pow k) sums
             (1 / (1 - 2 * x - x pow 2)))
      ==>
      !n : num.
        ?m : num.
          a n pow 2 + a (n + 1) pow 2 = a m``;
