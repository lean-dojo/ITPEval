(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_b3:
  the classification of positive differentiable functions on the positive
  reals satisfying a derivative functional equation. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory transcTheory derivativeTheory;

val putnam_2005_b3 =
  ``!f : real -> real.
      ((!x : real. 0 < x ==> 0 < f x) /\
       f differentiable_on {x : real | 0 < x})
      ==>
      ((?a : real.
          0 < a /\
          !x : real.
            0 < x
            ==>
            vector_derivative f (at (a / x)) = x / f x)
       <=>
       ?c d : real.
         0 < c /\
         0 < d /\
         (d = 1 ==> c = 1) /\
         !x : real.
           0 < x ==> f x = c * x powr d)``;
