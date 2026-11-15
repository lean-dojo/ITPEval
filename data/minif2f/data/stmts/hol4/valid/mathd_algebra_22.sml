(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_22: the real logarithm
  identity log base 25 of 625 equals 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val mathd_algebra_22 =
  ``ln (&(5 EXP 4)) / ln (&(5 EXP 2)) = (2 : real)``;
