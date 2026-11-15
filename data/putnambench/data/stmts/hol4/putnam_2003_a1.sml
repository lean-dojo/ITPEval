(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_a1:
  the number of nondecreasing sums of a positive integer into positive
  integers differing by at most one is the integer itself. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pred_setTheory;

val putnam_2003_a1 =
  ``!n : num.
      0 < n
      ==>
      CARD
        {a : int list |
           a <> [] /\
           FOLDR (\x acc : int. x + acc) 0 a = int_of_num n /\
           EVERY (\x : int. 0 < x) a /\
           (!i : num.
              SUC i < LENGTH a
              ==>
              EL i a <= EL (SUC i) a) /\
           LAST a <= HD a + 1} =
      n``;
