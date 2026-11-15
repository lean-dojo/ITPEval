(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a4
  (putnambench__hol4__putnam_2025_a4): the least dimension of 2025 real square
  matrices whose commuting pairs are exactly the equal, adjacent, and endpoint
  pairs is three. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_2025_a4 =
  ``let matrix_eq =
      \k : num.
      \A B : num -> num -> real.
        !r s : num.
          r < k /\ s < k ==> A r s = B r s
    in
    let matrix_mul =
      \k : num.
      \A B : num -> num -> real.
      \r s : num.
        if r < k /\ s < k
        then SIGMA (\t : num. A r t * B t s) (count k)
        else 0
    in
    let commute =
      \k : num.
      \A B : num -> num -> real.
        matrix_eq k (matrix_mul k A B) (matrix_mul k B A)
    in
    let admissible =
      \k : num.
        ?A : num -> num -> num -> real.
          !i j : num.
            i < 2025 /\ j < 2025 /\ i <= j
            ==>
            (commute k (A i) (A j) <=>
             j - i = 0 \/ j - i = 1 \/ j - i = 2024)
    in
      admissible 3 /\
      !k : num. admissible k ==> 3 <= k``;
