(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_393: evaluating at 33 the
  inverse of the real bijection x |-> 4 * x^3 + 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val _ = new_theory "hello";

val mathd_algebra_393 =
  ``!sigma inv_sigma : real -> real.
      (!x : real.
         sigma (inv_sigma x) = x /\
         inv_sigma (sigma x) = x) /\
      (!x : real. sigma x = 4 * x pow 3 + 1)
      ==>
      inv_sigma 33 = 2``;

val _ = export_theory();
