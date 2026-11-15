(*
  Statement-only formalization of miniF2F valid problem amc12b_2021_p21: bounds on the finite-set
  sum of the positive real solutions to a nested real-exponentiation equation. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory real_sigmaTheory;

val _ = new_theory "hello";

val amc12b_2021_p21 =
  ``!S : real set.
      FINITE S /\
      (!x : real.
         x IN S <=>
         0 < x /\
         x powr ((2 : real) powr (sqrt 2)) =
           (sqrt 2) powr ((2 : real) powr x))
      ==>
      2 <= SIGMA (\k. k) S /\
      SIGMA (\k. k) S < 6``;

val _ = export_theory();
