(*
  Statement-only formalization of miniF2F test problem amc12a_2009_p7: identifying the index
  of 2009 in a real arithmetic sequence determined by three specified terms. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val amc12a_2009_p7 =
  ``!x : real. !n : num. !a : num -> real.
      (!m : num.
         a (m + 1) - a m = a (m + 2) - a (m + 1)) /\
      a 1 = 2 * x - 3 /\
      a 2 = 5 * x - 11 /\
      a 3 = 3 * x + 1 /\
      a n = 2009
      ==>
      n = 502``;
