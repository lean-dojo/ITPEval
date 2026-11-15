(*
  Statement-only formalization of miniF2F test problem amc12a_2020_p9: counting the real
  solutions on [0, 2 * pi] of tan (2 * x) = cos (x / 2). This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory;

val amc12a_2020_p9 =
  ``let solution_set =
      {x : real |
         0 <= x /\ x <= 2 * pi /\
         tan (2 * x) = cos (x / 2)}
    in
      FINITE solution_set /\ CARD solution_set = 5``;
