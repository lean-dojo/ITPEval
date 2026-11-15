(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_b2:
  the one-eighth bound for initial integrals of a real function with
  continuous derivative and zero integral on the unit interval. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory derivativeTheory;
open integrationTheory;

val putnam_2007_b2 =
  ``let unit_interval = interval [0, 1]
    in
      !f : real -> real. !max_deriv : real.
        f differentiable_on unit_interval /\
        (\x : real.
           vector_derivative f (at x within unit_interval))
          continuous_on unit_interval /\
        integration$integral unit_interval f = 0 /\
        (?x : real.
           x IN unit_interval /\
           abs
             (vector_derivative f (at x within unit_interval)) =
           max_deriv) /\
        (!x : real.
           x IN unit_interval
           ==>
           abs
             (vector_derivative f (at x within unit_interval)) <=
           max_deriv)
        ==>
        !alpha : real.
          0 < alpha /\ alpha < 1
          ==>
          abs
            (integration$integral (interval [0, alpha]) f) <=
          (1 / 8) * max_deriv``;
