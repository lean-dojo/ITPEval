(*
  Statement-only formalization of miniF2F test problem amc12a_2020_p15: bounding the distance
  between complex roots satisfying two cubic equations. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory complexTheory;

val _ = new_theory "hello";

val amc12a_2020_p15 =
  ``!a b : complex.
      (a pow 3 - 8 = 0) /\
      (b pow 3 - 8 * (b pow 2) - 8 * b + 64 = 0)
      ==>
      modu (a - b) <= 2 * sqrt 21``;

val _ = export_theory();
