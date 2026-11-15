(*
  Statement-only formalization of miniF2F test problem amc12_2001_p21: a natural-number
  factorial and bilinear system whose integer endpoint difference is 10. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val amc12_2001_p21 =
  ``!a b c d : num.
      a * b * c * d = FACT 8 /\
      a * b + a + b = 524 /\
      b * c + b + c = 146 /\
      c * d + c + d = 104
      ==>
      int_of_num a - int_of_num d = (10 : int)``;
