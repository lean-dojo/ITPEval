(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_b5:
  a differentiable real function on x > 1 satisfying the given nonlinear
  differential equation tends to positive infinity. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory derivativeTheory;

val putnam_2009_b5 =
  ``!f : real -> real.
      f differentiable_on {x : real | 1 < x} /\
      (!x : real.
         1 < x
         ==>
         vector_derivative f (at x) =
           (x pow 2 - f x pow 2) /
           (x pow 2 * (f x pow 2 + 1)))
      ==>
      !B : real.
        ?A : real.
          !x : real. A <= x ==> B <= f x``;
