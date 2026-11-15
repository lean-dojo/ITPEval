(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a6:
  the determinant of the Hankel matrix formed from the local power-series
  coefficients of the specified square-root function is 10^(n(n-1)/2).
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory realTheory seqTheory;

val putnam_2024_a6 =
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
      !c : num -> real. !n : num.
        (?epsilon : real.
           0 < epsilon /\
           !x : real.
             abs x < epsilon
             ==>
             (\k : num. c k * x pow k) sums
               ((1 - 3 * x - sqrt (1 - 14 * x + 9 * x pow 2)) / 4)) /\
        0 < n
        ==>
        determinant n (\i j : num. c (i + j + 1)) =
        (10 : real) pow ((n * (n - 1)) DIV 2)``;
