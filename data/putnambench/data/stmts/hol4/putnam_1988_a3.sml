(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_a3:
  the real exponents for which the series with terms
  ((1/n) / sin(1/n) - 1)^x converges are exactly those greater than one half.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory transcTheory;

val putnam_1988_a3 =
  ``!x : real.
      (?L : real.
         ((\t : num.
             SIGMA
               (\n : num.
                  (((1 : real) / &n) / sin ((1 : real) / &n) - 1) powr x)
               (IMAGE SUC (count t))) --> L)
           sequentially)
      <=>
      x > 1 / 2``;
