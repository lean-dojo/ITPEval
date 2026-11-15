(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_a2:
  the determinant of the n by n real matrix whose (i,j)-entry is the
  reciprocal of min(i,j), with one-based indices, is the stated signed
  reciprocal product of consecutive factorials. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory realTheory;

val putnam_2014_a2 =
  ``let determinant =
      \n : num. \A : num -> num -> real.
        ITSET
          (\p : num -> num. \sum : real.
             (if evenperm p then
                ITSET
                  (\i : num. \acc : real. A i (p i) * acc)
                  (count n)
                  1
              else
                -(ITSET
                    (\i : num. \acc : real. A i (p i) * acc)
                    (count n)
                    1)) +
             sum)
          {p : num -> num | p permutes count n}
          0
    in
      !n : num. !A : num -> num -> real.
        0 < n /\
        (!i j : num.
           i < n /\ j < n
           ==>
           A i j = 1 / &(MIN (SUC i) (SUC j)))
        ==>
        determinant n A =
          (-1 : real) pow (n - 1) /
          (&(FACT (n - 1)) * &(FACT n))``;
