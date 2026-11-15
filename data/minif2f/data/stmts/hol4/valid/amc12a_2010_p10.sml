(*
  Statement-only formalization of miniF2F valid problem amc12a_2010_p10: a real-valued
  arithmetic progression with specified terms has value 8041 at index 2010. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val amc12a_2010_p10 =
  ``!p q : real. !a : num -> real.
      (!n : num.
         a (n + 2) - a (n + 1) = a (n + 1) - a n) /\
      a 1 = p /\
      a 2 = 9 /\
      a 3 = 3 * p - q /\
      a 4 = 3 * p + q
      ==>
      a 2010 = 8041``;
