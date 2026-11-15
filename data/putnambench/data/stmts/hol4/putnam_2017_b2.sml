(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_b2:
  the least positive starting integer whose sum of 2017 consecutive positive
  integers has no other consecutive-positive-integer representation of length
  greater than one is 16. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2017_b2 =
  ``let consecutive_sum =
      \a : int.
      \k : num.
        ITSET
          (\i acc. a + int_of_num i + acc)
          (count k)
          (0 : int)
    in
    let valid_start =
      \a : int.
        0 < a /\
        !b : int. !k : num.
          0 < b /\
          1 < k /\
          consecutive_sum a 2017 = consecutive_sum b k
          ==>
          k = 2017
    in
      valid_start 16 /\
      !a : int. valid_start a ==> 16 <= a``;
