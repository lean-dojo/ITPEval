(*
  Statement-only formalization of PutnamBench artifact putnam_1966_b2:
  among any ten consecutive positive integers, one is relatively prime to
  every other integer in the ten-member set. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory integerTheory pred_setTheory;

val putnam_1966_b2 =
  ``let S =
      \n : int.
        {m : int |
          m = n \/
          m = n + 1 \/
          m = n + 2 \/
          m = n + 3 \/
          m = n + 4 \/
          m = n + 5 \/
          m = n + 6 \/
          m = n + 7 \/
          m = n + 8 \/
          m = n + 9}
    in
      !n : int.
        0 < n
        ==>
        ?k : int.
          k IN S n /\
          !m : int.
            m IN S n /\ k <> m
            ==>
            coprime (Num (ABS m)) (Num (ABS k))``;
