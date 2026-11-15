(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_b5:
  existence of a natural number that is a three-digit palindrome in at least
  2002 different bases. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory numposrepTheory pred_setTheory;

val putnam_2002_b5 =
  ``?n : num.
      2002 <=
      CARD
        {b : num |
           1 <= b /\
           LENGTH (n2l b n) = 3 /\
           n2l b n = REVERSE (n2l b n)}``;
