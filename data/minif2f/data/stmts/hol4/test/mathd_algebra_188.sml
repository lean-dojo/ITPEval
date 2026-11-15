(*
  Statement-only formalization of miniF2F test artifact mathd_algebra_188: a real bijection
  whose value and inverse value agree at 2 is involutive at 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_188 =
  ``!sigma inv_sigma : real -> real.
      (!x : real.
         sigma (inv_sigma x) = x /\
         inv_sigma (sigma x) = x) /\
      sigma 2 = inv_sigma 2
      ==>
      sigma (sigma 2) = 2``;
