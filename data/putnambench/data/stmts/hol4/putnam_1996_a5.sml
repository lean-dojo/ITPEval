(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_a5:
  for a prime p greater than 3 and k = floor(2p/3), p squared divides the
  sum of the binomial coefficients binomial p i for 1 <= i <= k. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory dividesTheory pred_setTheory;

val putnam_1996_a5 =
  ``!p k : num.
      prime p /\ 3 < p /\ k = (2 * p) DIV 3
      ==>
      divides (p EXP 2)
        (SIGMA
           (\i : num. binomial p i)
           (IMAGE SUC (count k)))``;
