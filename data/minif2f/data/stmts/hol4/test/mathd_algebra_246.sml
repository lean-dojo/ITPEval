(*
  Statement-only formalization of miniF2F test problem mathd_algebra_246: a quartic-form real
  function's value at -3 determines its value at 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_246 =
  ``!a b : real. !f : real -> real.
      (!x : real.
         f x = a * x pow 4 - b * x pow 2 + x + 5) /\
      f (-3) = 2
      ==>
      f 3 = 8``;
