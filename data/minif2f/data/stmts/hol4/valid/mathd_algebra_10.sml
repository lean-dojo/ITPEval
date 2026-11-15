(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_10: an absolute-value
  equality comparing two percentage calculations over the real numbers. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_10 =
  ``abs (((120 : real) / 100) * 30 - (130 / 100) * 20) = 10``;
