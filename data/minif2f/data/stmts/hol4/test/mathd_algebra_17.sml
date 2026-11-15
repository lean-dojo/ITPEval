(*
  Statement-only formalization of miniF2F test problem mathd_algebra_17: a nested real
  equation using the source-totalized square root determines the variable as 8.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val mathd_algebra_17 =
  ``!a : real.
      (if 0 <=
            4 + (if 0 <= 16 + 16 * a then sqrt (16 + 16 * a) else 0)
       then
         sqrt
           (4 + (if 0 <= 16 + 16 * a then sqrt (16 + 16 * a) else 0))
       else 0) +
      (if 0 <=
            1 + (if 0 <= 1 + a then sqrt (1 + a) else 0)
       then
         sqrt
           (1 + (if 0 <= 1 + a then sqrt (1 + a) else 0))
       else 0) = 6
      ==>
      a = 8``;
