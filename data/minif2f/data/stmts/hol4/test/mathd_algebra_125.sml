(*
  Statement-only formalization of miniF2F test problem mathd_algebra_125: a positive-natural
  linear system with integer subtraction that determines x = 6. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val mathd_algebra_125 =
  ``!x y : num.
      0 < x /\
      0 < y /\
      5 * x = y /\
      (int_of_num x - 3) + (int_of_num y - 3) = (30 : int)
      ==>
      x = 6``;
