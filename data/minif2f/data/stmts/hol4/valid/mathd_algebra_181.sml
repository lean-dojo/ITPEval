(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_181: solving a real
  rational equation with a nonzero denominator. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_181 =
  ``!n : real.
      n <> 3 /\
      (n + 5) / (n - 3) = 2
      ==>
      n = 11``;
