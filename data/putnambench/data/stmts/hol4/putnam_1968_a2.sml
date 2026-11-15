(*
  Statement-only formalization of PutnamBench artifact putnam_1968_a2:
  rational simultaneous approximation of two integer linear forms with
  nonzero determinant and arbitrarily small nonzero errors. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory ratTheory real_of_ratTheory;

val putnam_1968_a2 =
  ``!a b c d e f : int. !epsilon : real.
      a * d <> b * c /\
      0 < epsilon
      ==>
      ?r s : rat.
        0 <
          abs
            (real_of_rat r * real_of_int a +
             real_of_rat s * real_of_int b -
             real_of_int e) /\
        abs
            (real_of_rat r * real_of_int a +
             real_of_rat s * real_of_int b -
             real_of_int e) <
          epsilon /\
        0 <
          abs
            (real_of_rat r * real_of_int c +
             real_of_rat s * real_of_int d -
             real_of_int f) /\
        abs
            (real_of_rat r * real_of_int c +
             real_of_rat s * real_of_int d -
             real_of_int f) <
          epsilon``;
