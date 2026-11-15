(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_455: a nested real
  multiplication equation determines x as 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_455 =
  ``!x : real.
      2 * (2 * (2 * (2 * x))) = 48
      ==>
      x = 3``;
