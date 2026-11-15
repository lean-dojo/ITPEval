(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_159:
  determining a real coefficient from a quartic polynomial function value.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_159 =
  ``!b : real. !f : real -> real.
      (!x : real.
        f x =
          3 * x pow 4 - 7 * x pow 3 + 2 * x pow 2 - b * x + 1) /\
      f 1 = 1
      ==>
      b = -2``;
