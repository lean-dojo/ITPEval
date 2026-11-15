(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_b5:
  the number of endofunctions on {1,...,n} whose every orbit eventually
  reaches {1,...,k}. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_2013_b5 =
  ``!n k : num.
      0 < n /\ k IN IMAGE SUC (count n)
      ==>
      let X = IMAGE SUC (count n)
      in
        CARD
          {f : num -> num |
             (!x : num. x IN X ==> f x IN X) /\
             (!x : num. x NOTIN X ==> f x = 0) /\
             (!x : num.
                x IN X
                ==>
                ?j : num. FUNPOW f j x <= k)} =
        k * n EXP (n - 1)``;
