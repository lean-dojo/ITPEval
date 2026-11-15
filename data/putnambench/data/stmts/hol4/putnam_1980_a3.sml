(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1980_a3:
  evaluation of the integral of 1 / (1 + (tan x)^(sqrt 2)) from zero to
  pi / 2 as pi / 4. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory extrealTheory measureTheory;
open lebesgueTheory lebesgue_measureTheory;

val putnam_1980_a3 =
  ``lebesgue$integral
      (restrict_space lebesgue
        {x : real | 0 < x /\ x < pi / 2})
      (\x : real.
         Normal (1 / (1 + (tan x) powr (sqrt 2)))) =
    Normal (pi / 4)``;
