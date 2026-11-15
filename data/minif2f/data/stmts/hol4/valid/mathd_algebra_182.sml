(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_182: a distributive
  identity in complex arithmetic. This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val mathd_algebra_182 =
  ``!y : complex.
      7 * (3 * y + 2) = 21 * y + 14``;
