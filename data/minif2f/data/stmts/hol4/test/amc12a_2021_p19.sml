(*
  Statement-only formalization of miniF2F test problem amc12a_2021_p19: counting the real
  solutions on [0, pi] of sin ((pi / 2) * cos x) = cos ((pi / 2) * sin x). This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory;

val amc12a_2021_p19 =
  ``let solution_set =
      {x : real |
         0 <= x /\ x <= pi /\
         sin (pi / 2 * cos x) = cos (pi / 2 * sin x)}
    in
      FINITE solution_set /\ CARD solution_set = 2``;
