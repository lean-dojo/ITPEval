(*
  Statement-only formalization of miniF2F test problem amc12a_2019_p12: a squared
  base-2 logarithmic ratio determined by a product constraint. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val _ = new_theory "hello";

val amc12a_2019_p12 =
  ``!x y : real.
      0 < x /\ 0 < y /\
      ~(x = 1) /\ ~(y = 1) /\
      (ln x / ln 2 = ln 16 / ln y) /\
      (x * y = 64)
      ==>
      (ln (x / y) / ln 2) pow 2 = 20``;

val _ = export_theory();
