(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_b4:
  the average reciprocal weight of integer unit-step walks of length 4040
  that start and end at zero is 1 / 4040. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory
     real_sigmaTheory transcTheory;

val putnam_2020_b4 =
  ``let V =
      \n : num.
        {s : num -> int |
           s 0 = 0 /\
           (!j : num. 2 * n <= j ==> s j = 0) /\
           (!j : num.
              j IN IMAGE SUC (count (2 * n))
              ==>
              ABS (s j - s (j - 1)) = 1)}
    in
    let q =
      \n : num.
      \s : num -> int.
        (1 : real) +
        SIGMA
          (\j : num. (3 : real) powr real_of_int (s j))
          (IMAGE SUC (count (2 * n - 1)))
    in
    let M =
      \n : num.
        SIGMA
          (\v : num -> int. (1 : real) / q n v)
          (V n) /
        &(CARD (V n))
    in
      M 2020 = (1 : real) / 4040``;
