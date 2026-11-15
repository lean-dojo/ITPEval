(*
  Statement-only formalization of PutnamBench artifact putnam_1976_a4:
  a real root of an irreducible integer cubic, whose translate is a root of
  a second integer cubic, has one of two explicit companion roots. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory ratTheory realTheory intrealTheory;

val putnam_1976_a4 =
  ``!a b c d : int. !r : real.
      (r pow 3 +
       real_of_int a * r pow 2 +
       real_of_int b * r -
       1 = 0) /\
      (!q : rat.
         q * q * q +
         rat_of_int a * q * q +
         rat_of_int b * q -
         1 <> 0) /\
      ((r + 1) pow 3 +
       real_of_int c * (r + 1) pow 2 +
       real_of_int d * (r + 1) +
       1 = 0)
      ==>
      ?s : real.
        s pow 3 +
        real_of_int a * s pow 2 +
        real_of_int b * s -
        1 = 0 /\
        (s = -1 / (r + 1) \/
         s = -(r + 1) / r)``;
