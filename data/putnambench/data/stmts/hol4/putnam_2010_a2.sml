(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_a2:
  the differentiable real functions whose derivative equals every positive-
  integer forward difference quotient are exactly the affine functions. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_topologyTheory;
open derivativeTheory;

val putnam_2010_a2 =
  ``{f : real -> real |
       f differentiable_on UNIV /\
       !x : real. !n : num.
         0 < n
         ==>
         vector_derivative f (at x) =
           (f (x + &n) - f x) / &n} =
    {f : real -> real |
       ?c d : real.
         !x : real. f x = c * x + d}``;
