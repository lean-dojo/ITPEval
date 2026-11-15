(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_b3:
  the real exponents for which every positive globally differentiable function
  with derivative greater than its value eventually dominates the associated
  exponential function. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory limTheory transcTheory;

val putnam_1994_b3 =
  ``{k : real |
       !f : real -> real.
         (!x : real.
            f differentiable x /\
            0 < f x /\
            f x < diffn 1 f x)
         ==>
         ?N : real.
           !x : real.
             N < x ==> exp (k * x) < f x} =
    {k : real | k < 1}``;
