(*
  Statement-only formalization of miniF2F test problem
  numbertheory_aoddbdiv4asqpbsqmod8eq1: if a is odd and b is a nonnegative
  multiple of 4, then a^2 + b^2 has remainder 1 modulo 8. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val numbertheory_aoddbdiv4asqpbsqmod8eq1 =
  ``!a b : int.
      (?k : int. a = 2 * k + 1) /\
      (4 : int) int_divides b /\
      0 <= b
      ==>
      (a ** 2 + b ** 2) % 8 = 1``;
