(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_a5:
  linear dependence of a finite system of differentiable real functions
  satisfying a constant-coefficient linear ODE with strictly positive
  coefficients and tending componentwise to zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory limTheory;

val putnam_1995_a5 =
  ``let putnam_1995_a5_solution = T
    in
      putnam_1995_a5_solution <=>
      !n : num.
      !x : num -> real -> real.
      !a : num -> num -> real.
        0 < n /\
        (!i : num.
           i < n
           ==>
           !t : real. x i differentiable t) /\
        (!i j : num.
           i < n /\ j < n
           ==>
           0 < a i j) /\
        (!t : real.
         !i : num.
           i < n
           ==>
           diffn 1 (x i) t =
             SIGMA (\j : num. a i j * x j t) (count n)) /\
        (!i : num.
           i < n
           ==>
           (x i --> 0) at_posinfinity)
        ==>
        ~(!b : num -> real.
            (!t : real.
               SIGMA (\i : num. b i * x i t) (count n) = 0)
            ==>
            (!i : num. i < n ==> b i = 0))``;
