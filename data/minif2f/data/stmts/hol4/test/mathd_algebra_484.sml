(*
  Statement-only formalization of miniF2F test problem mathd_algebra_484: the real
  natural-logarithm identity ln 27 divided by ln 3 equals 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val mathd_algebra_484 =
  ``ln (&27) / ln (&3) = (3 : real)``;
