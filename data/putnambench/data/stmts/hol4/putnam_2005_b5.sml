(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_b5:
  a real multivariate polynomial with zero Laplacian that is divisible by the
  sum of the squares of its variables is identically zero. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_2005_b5 =
  ``let support =
      \P : (num -> num) -> real.
        {a : num -> num | P a <> 0}
    in
    let polynomial =
      \n : num.
      \P : (num -> num) -> real.
        FINITE (support P) /\
        !a : num -> num.
          a IN support P
          ==>
          !i : num. n <= i ==> a i = 0
    in
    let basis_square =
      \i : num.
      \j : num.
        if j = i then 2 else 0
    in
    let sum_squares =
      \n : num.
      \a : num -> num.
        REAL_SUM_IMAGE
          (\i : num. if a = basis_square i then 1 else 0)
          (count n)
    in
    let partial =
      \i : num.
      \P : (num -> num) -> real.
      \a : num -> num.
        &(SUC (a i)) *
        P (\j : num. if j = i then SUC (a i) else a j)
    in
    let poly_mul =
      \P Q : (num -> num) -> real.
      \a : num -> num.
        REAL_SUM_IMAGE
          (\PQ : (num -> num) # (num -> num).
             P (FST PQ) * Q (SND PQ))
          {PQ : (num -> num) # (num -> num) |
             PQ IN support P CROSS support Q /\
             !i : num. a i = (FST PQ) i + (SND PQ) i}
    in
      !n : num.
      !P : (num -> num) -> real.
        0 < n /\
        polynomial n P /\
        (!a : num -> num.
           REAL_SUM_IMAGE
             (\i : num. partial i (partial i P) a)
             (count n) =
           0) /\
        (?Q : (num -> num) -> real.
           polynomial n Q /\
           !a : num -> num.
             P a = poly_mul (sum_squares n) Q a)
        ==>
        P = (\a : num -> num. 0)``;
