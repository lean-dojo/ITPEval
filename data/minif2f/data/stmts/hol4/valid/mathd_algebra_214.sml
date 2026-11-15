(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_214: a real quadratic
  function determined at 4 and evaluated at 6. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_214 =
  ``!a : real. !f : real -> real.
      (!x : real. f x = a * (x - 2) pow 2 + 3) /\
      f 4 = 4
      ==>
      f 6 = 7``;
