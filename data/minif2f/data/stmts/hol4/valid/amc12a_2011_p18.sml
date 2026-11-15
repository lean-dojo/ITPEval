(*
  Statement-only formalization of miniF2F valid problem amc12a_2011_p18: a sharp real
  quadratic inequality under an absolute-value constraint. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val amc12a_2011_p18 =
  ``!x y : real.
      abs (x + y) + abs (x - y) = 2
      ==>
      x pow 2 - 6 * x + y pow 2 <= 8``;
