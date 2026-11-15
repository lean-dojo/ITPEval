(*
  Statement-only formalization of miniF2F valid artifact imo_1977_p5: a natural-number
  quotient-remainder system classifying two natural numbers by their integer distances from
  22. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val imo_1977_p5 =
  ``!a b q r : num.
      r < a + b /\
      a ** 2 + b ** 2 = (a + b) * q + r /\
      q ** 2 + r = 1977
      ==>
      (ABS (int_of_num a - 22) = 15 /\
       ABS (int_of_num b - 22) = 28) \/
      (ABS (int_of_num a - 22) = 28 /\
       ABS (int_of_num b - 22) = 15)``;
