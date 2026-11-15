(*
  Statement-only formalization of miniF2F test problem amc12b_2021_p18. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory complexTheory;

val amc12b_2021_p18 =
  ``!z : complex.
      12 * (modu z) pow 2 =
        2 * (modu (z + 2)) pow 2 +
        (modu (z pow 2 + 1)) pow 2 + 31
      ==>
      z + 6 / z = -2``;
