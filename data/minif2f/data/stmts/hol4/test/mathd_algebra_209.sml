(*
  Statement-only formalization of miniF2F test problem mathd_algebra_209: a real bijection with
  three specified inverse values has a prescribed double application. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_209 =
  ``!sigma inv_sigma : real -> real.
      (!x : real.
         sigma (inv_sigma x) = x /\
         inv_sigma (sigma x) = x) /\
      inv_sigma 2 = 10 /\
      inv_sigma 10 = 1 /\
      inv_sigma 1 = 2
      ==>
      sigma (sigma 10) = 1``;
