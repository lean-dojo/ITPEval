(*
  Statement-only formalization of miniF2F test problem mathd_algebra_107:
  completing the square for a real circle equation. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_107 =
  ``!x y : real.
      x pow 2 + 8 * x + y pow 2 - 6 * y = 0
      ==>
      (x + 4) pow 2 + (y - 3) pow 2 = 5 pow 2``;
