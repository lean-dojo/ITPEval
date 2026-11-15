(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_b1:
  the positive integers within 250 of exactly 15 perfect squares are precisely
  those in the intervals from 315 to 325 and from 332 to 350. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_1994_b1 =
  ``!n : int.
      let nearby_squares =
        {m : num |
           ABS (n - int_of_num (m EXP 2)) <= 250}
      in
        (((315 : int) <= n /\ n <= 325) \/
         (332 <= n /\ n <= 350))
        <=>
        (0 < n /\
         FINITE nearby_squares /\
         CARD nearby_squares = 15)``;
