(*
  Statement-only formalization of miniF2F test artifact mathd_algebra_142: two real linear
  equations imply that m + b = 5. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val _ = new_theory "hello";

val mathd_algebra_142 =
  ``!m b : real.
      m * 7 + b = -1 /\
      m * (-1) + b = 7
      ==>
      m + b = 5``;

val _ = export_theory();
