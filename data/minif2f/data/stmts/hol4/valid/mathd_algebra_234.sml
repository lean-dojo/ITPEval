(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_234: a real linear
  equation determining a cubic expression. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_234 =
  ``!d : real.
      (27 / 125 * d = 9 / 25)
      ==>
      (3 / 5 * d pow 3 = 25 / 9)``;
