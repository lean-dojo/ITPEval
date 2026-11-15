(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_b6
  (putnambench__hol4__putnam_2023_b6): the determinant of the matrix counting
  nonnegative integer solutions to a*i + b*j = n has the specified alternating
  closed form. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory permutesTheory;

val putnam_2023_b6 =
  ``let determinant =
      \n : num. \A : num -> num -> int.
        ITSET
          (\p : num -> num. \sum : int.
             (if evenperm p then 1 else ~1) *
             ITSET
               (\i : num. \acc : int. A i (p i) * acc)
               (count n)
               (1 : int) +
             sum)
          {p : num -> num | p permutes count n}
          (0 : int)
    in
      !n : num. !S : num -> num -> int.
        0 < n /\
        (!i j : num.
           i < n /\ j < n
           ==>
           S i j =
             int_of_num
               (CARD
                  {ab : num # num |
                     FST ab * (i + 1) + SND ab * (j + 1) = n}))
        ==>
        determinant n S =
          (~1 : int) ** ((n + 1) DIV 2 + 1) *
          int_of_num (2 * ((n + 1) DIV 2))``;
