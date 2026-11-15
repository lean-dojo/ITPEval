(*
  Statement-only formalization of miniF2F test problem mathd_algebra_208: the square root of
  one million minus its real cube root equals 900. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val mathd_algebra_208 =
  ``sqrt (1000000 : real) -
      (1000000 : real) powr (1 / 3 : real) = 900``;
