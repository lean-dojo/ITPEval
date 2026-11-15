(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_b2:
  the limit of the factorial-normalized iterated integrals of the real
  logarithm at one is -1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory;
open real_topologyTheory integrationTheory;

val putnam_2008_b2 =
  ``!F : num -> real -> real.
      (!x : real. F 0 x = ln x) /\
      (!n : num. !x : real.
         0 < x
         ==>
         F (n + 1) x =
           integration$integral (interval [0, x]) (F n))
      ==>
      (((\n : num.
           &(FACT n) * F n 1 / ln (&n)) -->
        (~1 : real))
       sequentially)``;
