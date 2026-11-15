(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_b5:
  evaluation of an improper integral on the positive real half-line, assuming
  the Gaussian integral over the real line. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory extrealTheory measureTheory;
open lebesgueTheory lebesgue_measureTheory;

val putnam_1985_b5 =
  ``lebesgue$integral lebesgue
      (\x : real. Normal (exp (-(x pow 2)))) =
      Normal (sqrt pi)
    ==>
    lebesgue$integral
      (restrict_space lebesgue {t : real | 0 < t})
      (\t : real.
         Normal
           (t powr (-(1 : real) / 2) *
            exp (-1985 * (t + t powr (-(1 : real)))))) =
      Normal (sqrt (pi / 1985) * exp (-3970))``;
