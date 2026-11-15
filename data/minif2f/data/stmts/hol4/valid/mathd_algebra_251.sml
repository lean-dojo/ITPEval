(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_251: solving the real
  rational equation 3 + 1/x = 7/x under the assumption x <> 0. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_251 =
  ``!x : real.
      x <> 0 /\
      3 + 1 / x = 7 / x
      ==>
      x = 2``;
