(*
  Statement-only formalization of PutnamBench artifact putnam_1980_a4:
  existence of a bounded nonzero integer linear combination of 1, sqrt 2,
  and sqrt 3 below 10^-11, with all such combinations above 10^-21.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory transcTheory;

val putnam_1980_a4 =
  ``let abcvals =
      \a b c : int.
        ~(a = 0 /\ b = 0 /\ c = 0) /\
        Num (ABS a) < 1000000 /\
        Num (ABS b) < 1000000 /\
        Num (ABS c) < 1000000
    in
      (?a b c : int.
         abcvals a b c /\
         abs
           (real_of_int a +
            real_of_int b * sqrt 2 +
            real_of_int c * sqrt 3) <
           1 / ((10 : real) pow 11)) /\
      (!a b c : int.
         abcvals a b c
         ==>
         abs
           (real_of_int a +
            real_of_int b * sqrt 2 +
            real_of_int c * sqrt 3) >
           1 / ((10 : real) pow 21))``;
