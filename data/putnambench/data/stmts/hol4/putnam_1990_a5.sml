(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_a5:
  the assertion that ABAB = 0 implies BABA = 0 for all nonempty square real
  matrices is false. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_1990_a5 =
  ``let matrix_mul =
      \n : num.
      \A B : num -> num -> real.
      \i j : num.
        SIGMA (\k : num. A i k * B k j) (count n)
    in
    let matrix_zero =
      \n : num.
      \A : num -> num -> real.
        !i j : num.
          i < n /\ j < n ==> A i j = 0
    in
      ((!n : num. !A B : num -> num -> real.
          1 <= n
          ==>
          matrix_zero n
            (matrix_mul n (matrix_mul n (matrix_mul n A B) A) B)
          ==>
          matrix_zero n
            (matrix_mul n (matrix_mul n (matrix_mul n B A) B) A))
       <=> F)``;
