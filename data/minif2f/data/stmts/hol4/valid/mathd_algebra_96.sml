(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_96: logarithmic differences
  among positive real numbers force a = -8. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val _ = new_theory "hello";

val mathd_algebra_96 =
  ``!x y z a : real.
      0 < x /\
      0 < y /\
      0 < z /\
      ln x - ln y = a /\
      ln y - ln z = 15 /\
      ln z - ln x = -7
      ==>
      a = -8``;

val _ = export_theory();
