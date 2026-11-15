(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_247: two real algebraic
  equations with an integer exponent fixed at 3 imply t = 0. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory transcTheory;

val mathd_algebra_247 =
  ``!t s : real. !n : int.
      t = 2 * s - s pow 2 /\
      s =
        real_of_int (n ** 2) -
          exp (real_of_int n * ln 2) + 1 /\
      n = 3
      ==>
      t = 0``;
