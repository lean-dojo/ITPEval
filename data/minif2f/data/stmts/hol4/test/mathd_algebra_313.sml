(*
  Statement-only formalization of miniF2F artifact mathd_algebra_313: solving v = x * z over
  the complex numbers from v = 1 + i and z = 2 - i gives
  x = 1 / 5 + (3 / 5) * i. This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val mathd_algebra_313 =
  ``!v x z : complex.
      (v = x * z) /\
      (v = 1 + i) /\
      (z = 2 - i)
      ==>
      x = 1 / 5 + (3 / 5) * i``;
