(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_b1:
  3987 is the least positive integer n such that every integer m strictly
  between 0 and 1993 admits an integer k with
  m/1993 < k/n < (m+1)/1994. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory;

val putnam_1993_b1 =
  ``let admissible =
      \n : num.
        0 < n /\
        !m : int.
          0 < m /\ m < 1993
          ==>
          ?k : int.
            real_of_int m / 1993 <
              real_of_int k / (&n : real) /\
            real_of_int k / (&n : real) <
              real_of_int (m + 1) / 1994
    in
      admissible 3987 /\
      !n : num. admissible n ==> 3987 <= n``;
