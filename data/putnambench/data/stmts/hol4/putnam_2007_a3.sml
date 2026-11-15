(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_a3:
  the probability that no nonempty prefix sum of a random ordering of the
  integers from 1 through 3k+1 is divisible by 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory permutesTheory realTheory;

val putnam_2007_a3 =
  ``!k : num.
      0 < k
      ==>
      let n = 3 * k + 1
      in
        &(CARD
            {p : num -> num |
               p permutes count n /\
               !j : num.
                 j < n
                 ==>
                 ~divides 3
                    (SIGMA (\i : num. p i + 1) (count (j + 1)))}) /
        &(CARD {p : num -> num | p permutes count n}) =
        (&(FACT k) * &(FACT (k + 1))) /
        ((&(3 * k + 1) : real) * &(FACT (2 * k)))``;
