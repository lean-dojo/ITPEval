(*
  Statement-only formalization of miniF2F test problem amc12b_2020_p22: a universal
  real-exponential inequality with upper bound 1/12. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val _ = new_theory "hello";

val amc12b_2020_p22 =
  ``!t : real.
      ((2 powr t - 3 * t) * t) / (4 powr t) <= 1 / 12``;

val _ = export_theory();
