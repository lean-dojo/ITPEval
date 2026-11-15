(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_437: real cubic constraints
  and strict bounds placing an integer between two real values imply that the integer is -4.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory;

val mathd_algebra_437 =
  ``!x y : real. !n : int.
      x pow 3 = -45 /\
      y pow 3 = -101 /\
      x < real_of_int n /\
      real_of_int n < y
      ==>
      n = -4``;
