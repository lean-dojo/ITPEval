(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_a3:
  a sequence initialized by x_k = k for 1 <= k <= 2006 and satisfying the
  given recurrence has 2005 consecutive terms divisible by 2006. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val putnam_2006_a3 =
  ``!x : num -> num.
      (!k : num. 1 <= k /\ k <= 2006 ==> x k = k) /\
      (!k : num.
         2006 <= k
         ==>
         x (k + 1) = x k + x (k - 2005))
      ==>
      ?i : num.
        0 < i /\
        !j : num.
          j < 2005
          ==>
          divides 2006 (x (i + j))``;
