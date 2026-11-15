(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_48. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val mathd_algebra_48 =
  ``!q e : complex.
      (q = 9 - 4 * i) /\
      (e = ~3 - 4 * i)
      ==>
      q - e = 12``;
