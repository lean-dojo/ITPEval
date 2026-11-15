(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_b6:
  entrywise powers of a positive-dimensional real square matrix agree with
  its ordinary matrix powers for all positive exponents if they agree through
  exponent n + 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_2010_b6 =
  ``let matrix_eq =
      \n : num.
      \A B : num -> num -> real.
        !i j : num.
          i < n /\ j < n ==> A i j = B i j
    in
    let matrix_mul =
      \n : num.
      \A B : num -> num -> real.
      \i j : num.
        if i < n /\ j < n
        then SIGMA (\r : num. A i r * B r j) (count n)
        else 0
    in
    let matrix_one =
      \n : num.
      \i j : num.
        if i < n /\ j < n /\ i = j then 1 else 0
    in
    let matrix_pow =
      \n : num.
      \A : num -> num -> real.
      \k : num.
        FUNPOW
          (\B : num -> num -> real. matrix_mul n B A)
          k (matrix_one n)
    in
    let entrywise_pow =
      \A : num -> num -> real.
      \k : num.
      \i j : num.
        A i j pow k
    in
      !n : num.
      !A : num -> num -> real.
        1 <= n
        ==>
        ((!k : num.
            1 <= k /\ k <= n + 1
            ==>
            matrix_eq n (matrix_pow n A k) (entrywise_pow A k))
         ==>
         !k : num.
           1 <= k
           ==>
           matrix_eq n (matrix_pow n A k) (entrywise_pow A k))``;
