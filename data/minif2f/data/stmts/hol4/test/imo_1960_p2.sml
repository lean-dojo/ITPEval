(*
  Statement-only formalization of miniF2F test problem imo_1960_p2: a real inequality involving
  a square root that bounds the variable in an interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val imo_1960_p2 =
  ``!x : real.
      0 <= 1 + 2 * x /\
      ~((1 - sqrt (1 + 2 * x)) pow 2 = 0) /\
      (4 * x pow 2) / ((1 - sqrt (1 + 2 * x)) pow 2) < 2 * x + 9 /\
      ~(x = 0)
      ==>
      -(1 / 2) <= x /\ x < 45 / 8``;
