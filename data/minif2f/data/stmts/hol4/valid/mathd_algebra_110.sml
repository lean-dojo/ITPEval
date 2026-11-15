(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_110. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val mathd_algebra_110 =
  ``!q e : complex.
      (q = 2 - 2 * i) /\
      (e = 5 + 5 * i)
      ==>
      q * e = 20``;
