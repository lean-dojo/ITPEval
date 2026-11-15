(*
  Statement-only formalization of miniF2F test problem mathd_algebra_478: substituting specified
  positive real values into v = (1 / 3) * (b * h). This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_478 =
  ``!b h v : real.
      (0 < b /\ 0 < h /\ 0 < v) /\
      v = (1 / 3) * (b * h) /\
      b = 30 /\
      h = 13 / 2 ==>
      v = 65``;
