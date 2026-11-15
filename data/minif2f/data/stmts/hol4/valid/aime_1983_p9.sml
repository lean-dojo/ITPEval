(*
  Statement-only formalization of miniF2F valid problem aime_1983_p9: a trigonometric
  lower bound for a real number between 0 and pi. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val aime_1983_p9 =
  ``!x : real.
      0 < x /\ x < pi
      ==>
      12 <= (9 * (x pow 2 * (sin x) pow 2) + 4) / (x * sin x)``;
