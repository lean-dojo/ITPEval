(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_b6:
  uniqueness of unordered pairs of indices from zero through 99 whose
  associated integer pair-sums are congruent modulo 10100. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val putnam_1994_b6 =
  ``!n : num -> int.
      (!a : num.
         n a =
           101 * int_of_num a -
           100 * int_of_num (2 EXP a))
      ==>
      !a b c d : num.
        a <= 99 /\ b <= 99 /\ c <= 99 /\ d <= 99 /\
        (10100 : int) int_divides
          (n a + n b - (n c + n d))
        ==>
        (a = c /\ b = d) \/ (a = d /\ b = c)``;
