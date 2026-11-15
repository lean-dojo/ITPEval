(*
  Statement-only formalization of miniF2F test artifact amc12a_2003_p5: decimal digit arithmetic
  in which the digit patterns AMC10 and AMC12 sum to 123422, forcing A + M + C = 14. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val amc12a_2003_p5 =
  ``!a m c : num.
      (a <= 9 /\ m <= 9 /\ c <= 9) /\
      (10 * (10 * (10 * (10 * a + m) + c) + 1) + 0 +
       (10 * (10 * (10 * (10 * a + m) + c) + 1) + 2) = 123422)
      ==>
      a + m + c = 14``;
