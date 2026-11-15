(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_451: evaluating two
  applications of a real bijection from specified values of its inverse. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_451 =
  ``!sigma inv_sigma : real -> real.
      (!x : real.
         sigma (inv_sigma x) = x /\
         inv_sigma (sigma x) = x) /\
      inv_sigma (-15) = 0 /\
      inv_sigma 0 = 3 /\
      inv_sigma 3 = 9 /\
      inv_sigma 9 = 20
      ==>
      sigma (sigma 9) = 0``;
