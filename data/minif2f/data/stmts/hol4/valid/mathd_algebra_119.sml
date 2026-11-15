(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_119: solving two linear
  equations over the reals to determine e. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_119 =
  ``!d e : real.
      2 * d = 17 * e - 8 /\
      2 * e = d - 9
      ==>
      e = 2``;
