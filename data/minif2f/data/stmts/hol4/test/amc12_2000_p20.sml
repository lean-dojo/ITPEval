(*
  Statement-only formalization of miniF2F test problem amc12_2000_p20: positive real numbers
  satisfying a cyclic system of reciprocal equations, with conclusion that their product is
  one. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val _ = new_theory "hello";

val amc12_2000_p20 =
  ``!x y z : real.
      0 < x /\ 0 < y /\ 0 < z /\
      x + 1 / y = 4 /\
      y + 1 / z = 1 /\
      z + 1 / x = 7 / 3
      ==>
      x * y * z = 1``;

val _ = export_theory();
