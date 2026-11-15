(*
  Statement-only formalization of miniF2F artifact amc12b_2021_p3: a real continued-fraction
  equation determines x to be 3/4. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val amc12b_2021_p3 =
  ``!x : real.
      2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53
      ==>
      x = 3 / 4``;
