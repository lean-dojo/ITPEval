(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_a5:
  the greatest integer represented by exactly 2020 finite sets of positive
  Fibonacci indices having that Fibonacci sum. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2020_a5 =
  ``let is_fibonacci =
      \f : num -> num.
        f 0 = 0 /\
        f 1 = 1 /\
        (!k : num. f (k + 2) = f (k + 1) + f k)
    in
    let fibonacci =
      @f : num -> num. is_fibonacci f
    in
    let a =
      \n : int.
        CARD
          {s : num set |
             FINITE s /\
             (!k : num. k IN s ==> 0 < k) /\
             int_of_num (SIGMA fibonacci s) = n}
    in
    let solution =
      int_of_num (fibonacci 4040) - 1
    in
      a solution = 2020 /\
      (!n : int. a n = 2020 ==> n <= solution)``;
