(*
  Statement-only formalization of miniF2F test problem algebra_9onxpypzleqsum2onxpy:
  a reciprocal-sum inequality for three positive real numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val algebra_9onxpypzleqsum2onxpy =
  ``!x y z : real.
      0 < x /\ 0 < y /\ 0 < z
      ==>
      9 / (x + y + z) <=
        2 / (x + y) + 2 / (y + z) + 2 / (z + x)``;
