(*
  Statement-only formalization of miniF2F test problem mathd_algebra_452: an arithmetic
  progression of real numbers has value 11/15 at index 5 when its values at indices 1 and 9
  are 2/3 and 4/5. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val mathd_algebra_452 =
  ``!a : num -> real.
      (!n : num.
         a (n + 2) - a (n + 1) = a (n + 1) - a n) /\
      a 1 = 2 / 3 /\
      a 9 = 4 / 5
      ==>
      a 5 = 11 / 15``;
