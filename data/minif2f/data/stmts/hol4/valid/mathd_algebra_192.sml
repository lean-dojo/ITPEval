(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_192: the product of three
  specified complex numbers equals 292 times the imaginary unit. This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val mathd_algebra_192 =
  ``!q e d : complex.
      (q = 11 - 5 * i) /\
      (e = 11 + 5 * i) /\
      (d = 2 * i)
      ==>
      q * e * d = 292 * i``;
