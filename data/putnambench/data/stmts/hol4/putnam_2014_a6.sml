(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_a6:
  for positive n, the largest size of two indexed families of real n by n
  matrices whose products have a diagonal zero exactly for distinct family
  indices is n^n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_2014_a6 =
  ``let admissible =
      \n k : num.
        ?M N : num -> num -> num -> real.
          !i j : num.
            i < k /\ j < k
            ==>
            ((?p : num.
                p < n /\
                SIGMA
                  (\r : num. M i p r * N j r p)
                  (count n) =
                0) <=>
             i <> j)
    in
      !n : num.
        0 < n
        ==>
        (1 <= n EXP n /\ admissible n (n EXP n)) /\
        (!k : num.
           1 <= k /\ admissible n k
           ==>
           k <= n EXP n)``;
