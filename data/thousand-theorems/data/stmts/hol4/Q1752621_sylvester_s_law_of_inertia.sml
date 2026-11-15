(*
  Statement-only formalization of Thousand Theorems corpus artifact
  thousand-theorems__hol4__Q1752621, "Sylvester's law of inertia": every
  finite-dimensional real quadratic form is linearly equivalent to a
  diagonal weighted sum of squares whose weights are -1, 0, or 1. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val QuadraticForm_equivalent_one_zero_neg_one_weighted_sum_squared =
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
        SIGMA (\k : num. A i k * B k j) (count n)
    in
    let matrix_transpose =
      \A : num -> num -> real.
      \i j : num.
        A j i
    in
    let matrix_one =
      \n : num.
      \i j : num.
        if i < n /\ j < n /\ i = j then 1 else 0
    in
    let matrix_symmetric =
      \n : num.
      \A : num -> num -> real.
        !i j : num.
          i < n /\ j < n ==> A i j = A j i
    in
    let matrix_invertible =
      \n : num.
      \A : num -> num -> real.
        ?Ainv : num -> num -> real.
          matrix_eq n (matrix_mul n A Ainv) (matrix_one n) /\
          matrix_eq n (matrix_mul n Ainv A) (matrix_one n)
    in
    let diagonal =
      \n : num.
      \w : num -> real.
      \i j : num.
        if i < n /\ j < n /\ i = j then w i else 0
    in
      !n : num.
      !A : num -> num -> real.
        matrix_symmetric n A
        ==>
        ?w : num -> real.
        ?P : num -> num -> real.
          (!i : num.
             i < n ==> w i = -1 \/ w i = 0 \/ w i = 1) /\
          matrix_invertible n P /\
          matrix_eq n
            (matrix_mul n (matrix_transpose P)
              (matrix_mul n (diagonal n w) P))
            A``;
