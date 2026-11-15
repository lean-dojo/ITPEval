(*
  Statement-only formalization of miniF2F test problem amc12b_2021_p13: the given
  trigonometric equation has exactly six real solutions in the interval (0, 2 * pi]. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory;

val amc12b_2021_p13 =
  ``let solution_set =
      {x : real |
         0 < x /\ x <= 2 * pi /\
         1 - 3 * sin x + 5 * cos (3 * x) = 0}
    in
      FINITE solution_set /\ CARD solution_set = 6``;
