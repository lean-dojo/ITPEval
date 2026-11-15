(*
  Statement-only formalization of miniF2F test problem amc12a_2021_p18: a rational-to-real
  function additive under multiplication of positive rationals and mapping each prime to its
  real value is negative at 25/11. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory realTheory ratTheory;

val _ = new_theory "hello";

val amc12a_2021_p18 =
  ``!f : rat -> real.
      (!x y : rat.
         0q < x /\ 0q < y ==>
         f (x * y) = f x + f y) /\
      (!p : num. prime p ==> f (rat_of_num p) = &p)
      ==>
      f (25q / 11q) < 0``;

val _ = export_theory();
