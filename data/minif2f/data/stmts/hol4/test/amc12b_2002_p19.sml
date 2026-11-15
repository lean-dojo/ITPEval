(*
  Statement-only formalization of miniF2F test problem amc12b_2002_p19: the product of three
  positive real numbers satisfying a cyclic system of equations. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val _ = new_theory "hello";

val amc12b_2002_p19 =
  ``!a b c : real.
      0 < a /\ 0 < b /\ 0 < c /\
      a * (b + c) = 152 /\
      b * (c + a) = 162 /\
      c * (a + b) = 170
      ==>
      a * b * c = 720``;

val _ = export_theory();
