(*
  Statement-only formalization of miniF2F test problem mathd_algebra_296: an integer
  absolute-value calculation from a difference-of-squares expression. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val mathd_algebra_296 =
  ``ABS (((3491 : int) - 60) * (3491 + 60) - 3491 ** 2) = 3600``;
