(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_509: a closed real-number
  identity involving nested square roots and rational divisions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_509 =
  ``sqrt (((5 : real) / sqrt 80 + sqrt 845 / 9 + sqrt 45) / sqrt 5) =
    13 / 6``;
