(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_b5:
  the number of permutations of {1,...,n} that send adjacent inputs to values
  at distance at most two satisfies a constant integer recurrence equal to
  four for every n at least two. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory permutesTheory;

val putnam_2015_b5 =
  ``let interval =
      \n : num. IMAGE SUC (count n)
    in
    let P =
      \n : num.
        CARD
          {p : num -> num |
             p permutes (interval n) /\
             !i j : num.
               i IN interval n /\
               j IN interval n /\
               ABS (int_of_num i - int_of_num j) = 1
               ==>
               ABS (int_of_num (p i) - int_of_num (p j)) <= 2}
    in
      !n : num.
        2 <= n
        ==>
        int_of_num (P (n + 5)) -
        int_of_num (P (n + 4)) -
        int_of_num (P (n + 3)) +
        int_of_num (P n) =
        4``;
