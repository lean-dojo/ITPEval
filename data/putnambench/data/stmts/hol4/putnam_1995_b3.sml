(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_b3:
  the sum of determinants of the row-major digit matrices associated with all
  positive n-squared-digit decimal integers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory permutesTheory;

val putnam_1995_b3 =
  ``let digits_set =
      \n : num. \f : num -> num.
        f 0 <> 0 /\
        (!i : num. i < n ** 2 ==> f i <= 9) /\
        (!i : num. n ** 2 <= i ==> f i = 0)
    in
    let digits_to_matrix =
      \n : num. \f : num -> num. \i : num. \j : num.
        int_of_num (f (i * n + j))
    in
    let determinant =
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
      !n : num.
        0 < n
        ==>
        ITSET
          (\f : num -> num. \sum : int.
             determinant n (digits_to_matrix n f) + sum)
          {f : num -> num | digits_set n f}
          (0 : int) =
        if n = 1 then 45
        else if n = 2 then 10 * 45 ** 2
        else 0``;
