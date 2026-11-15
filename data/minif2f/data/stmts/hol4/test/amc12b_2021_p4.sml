(*
  Statement-only formalization of miniF2F artifact amc12b_2021_p4: positive natural numbers
  in the ratio 3 to 4 have weighted average (84m + 70a) / (m + a) equal to 76. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val amc12b_2021_p4 =
  ``!m a : num.
      0 < m /\ 0 < a /\
      ((&m : real) / &a = 3 / 4)
      ==>
      (84 * &m + 70 * &a) / (&m + &a) = 76``;
