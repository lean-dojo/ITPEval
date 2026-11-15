(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_190: evaluation of a
  rational arithmetic expression over the real numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_190 =
  ``((3 : real) / 8 + 7 / 8) / (4 / 5) = 25 / 16``;
