(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_b5:
  existence, for every positive integer k, of k real polynomials expressing
  the kth power of floor(n/k) for every integer n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pred_setTheory realTheory;
open intrealTheory polyTheory;

val putnam_2007_b5 =
  ``!k : num.
      0 < k
      ==>
      ?P : real list list.
        LENGTH P = k /\
        !n : int.
          let q =
            real_of_int
              (INT_FLOOR (real_of_int n / (&k : real)))
          in
            q pow k =
              SIGMA
                (\i : num.
                   poly (EL i P) (real_of_int n) * q pow i)
                (count k)``;
