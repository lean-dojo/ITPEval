(*
  Statement-only formalization of miniF2F test problem amc12a_2021_p3: natural-number sum,
  divisibility, and quotient constraints determining an integer difference. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory integerTheory;

val amc12a_2021_p3 =
  ``!x y : num.
      x + y = 17402 /\
      divides 10 x /\
      x DIV 10 = y
      ==>
      int_of_num x - int_of_num y = (14238 : int)``;
