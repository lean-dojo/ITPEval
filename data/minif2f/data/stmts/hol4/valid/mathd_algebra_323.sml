(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_323: evaluating the
  inverse of the real bijection x |-> x^3 - 8 in a nested expression. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_323 =
  ``!sigma inv_sigma : real -> real.
      (!x : real.
         sigma (inv_sigma x) = x /\
         inv_sigma (sigma x) = x) /\
      (!x : real. sigma x = x pow 3 - 8)
      ==>
      inv_sigma (sigma (inv_sigma 19)) = 3``;
