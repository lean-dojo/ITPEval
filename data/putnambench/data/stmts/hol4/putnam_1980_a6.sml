(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1980_a6:
  the greatest uniform lower bound of the integral of the absolute difference
  between a continuously differentiable function's derivative and its value
  on the unit interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory transcTheory derivativeTheory;
open extrealTheory measureTheory borelTheory lebesgueTheory;
open lebesgue_measureTheory;

val putnam_1980_a6 =
  ``let unit_interval = interval [0, 1]
    in
    let C =
      \f : real -> real.
        f differentiable_on unit_interval /\
        (\x : real.
           vector_derivative f (at x within unit_interval))
          continuous_on unit_interval /\
        f 0 = 0 /\
        f 1 = 1
    in
    let integral_value =
      \f : real -> real.
        real
          (lebesgue$integral
             (restrict_space lebesgue unit_interval)
             (\x : real.
                Normal
                  (abs
                     (vector_derivative f (at x within unit_interval) -
                      f x))))
    in
    let solution = 1 / exp 1
    in
      (!f : real -> real.
         C f
         ==>
         solution <= integral_value f) /\
      (!u : real.
         (!f : real -> real.
            C f
            ==>
            u <= integral_value f)
         ==>
         u <= solution)``;
