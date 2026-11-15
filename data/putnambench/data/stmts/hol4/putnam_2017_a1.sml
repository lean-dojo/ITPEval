(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_a1:
  the positive integers outside the least set containing 2 and closed under
  positive square roots and the stated shifted-square operation are exactly
  1 and the positive multiples of 5. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory;

val putnam_2017_a1 =
  ``let qualifying =
      \S : int set.
        (!n : int. n IN S ==> 0 < n) /\
        (2 : int) IN S /\
        (!n : int.
           0 < n /\ n ** 2 IN S
           ==>
           n IN S) /\
        (!n : int.
           n IN S
           ==>
           (n + 5) ** 2 IN S)
    in
      !S : int set.
        qualifying S /\
        (!T : int set. qualifying T ==> S SUBSET T)
        ==>
        {n : int | 0 < n /\ n NOTIN S} =
        {n : int |
           0 < n /\ (n = 1 \/ (5 : int) int_divides n)}``;
