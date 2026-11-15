(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_462: the closed fractional
  identity (1/2 + 1/3) * (1/2 - 1/3) = 5/36. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_462 =
  ``((1 : real) / 2 + 1 / 3) * (1 / 2 - 1 / 3) = 5 / 36``;
