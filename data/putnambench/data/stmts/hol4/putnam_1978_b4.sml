(*
  Statement-only formalization of PutnamBench artifact putnam_1978_b4:
  four integers can be chosen above any real threshold so that their squared
  sum equals the sum of their four triple products. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory;

val putnam_1978_b4 =
  ``!N : real.
      ?a b c d : int.
        N < real_of_int a /\
        N < real_of_int b /\
        N < real_of_int c /\
        N < real_of_int d /\
        a * a + b * b + c * c + d * d =
          a * b * c + a * b * d + a * c * d + b * c * d``;
