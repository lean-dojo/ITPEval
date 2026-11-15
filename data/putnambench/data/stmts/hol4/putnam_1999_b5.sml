(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_b5:
  the determinant of the n by n real matrix I + A, where
  A_jk = cos(j theta + k theta) and theta = 2 pi / n, is
  1 - n squared / 4. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory realTheory transcTheory;

val putnam_1999_b5 =
  ``let determinant =
      \n : num. \M : num -> num -> real.
        ITSET
          (\p : num -> num. \sum : real.
             (if evenperm p then
                ITSET
                  (\i : num. \acc : real. M i (p i) * acc)
                  (count n)
                  1
              else
                -(ITSET
                    (\i : num. \acc : real. M i (p i) * acc)
                    (count n)
                    1)) +
             sum)
          {p : num -> num | p permutes count n}
          0
    in
      !n : num. !theta : real. !A : num -> num -> real.
        3 <= n /\
        theta = 2 * pi / (&n : real) /\
        (!i j : num.
           i < n /\ j < n
           ==>
           A i j =
             cos ((&(SUC i) : real) * theta +
                  (&(SUC j) : real) * theta))
        ==>
        determinant n
          (\i j.
             (if i = j then 1 else 0) + A i j) =
        1 - (&n : real) pow 2 / 4``;
