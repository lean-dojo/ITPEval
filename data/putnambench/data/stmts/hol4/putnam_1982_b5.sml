(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1982_b5:
  convergence of an iterated logarithm sequence and continuity of its limit
  function for real x greater than exp (exp 1). This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_topologyTheory
     transcTheory;

val putnam_1982_b5 =
  ``!S : real -> num -> real.
      (!x : real.
         exp (exp 1) < x
         ==>
         S x 0 = exp 1 /\
         !n : num.
           S x (n + 1) = ln x / ln (S x n))
      ==>
      ?g : real -> real.
        (!x : real.
           exp (exp 1) < x
           ==>
           ((\n : num. S x n) --> g x) sequentially) /\
        g continuous_on {y : real | exp (exp 1) < y}``;
