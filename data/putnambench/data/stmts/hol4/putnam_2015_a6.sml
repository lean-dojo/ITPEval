(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_a6:
  positive-dimensional real square matrices satisfying A M = M B and having
  the same characteristic polynomial satisfy
  det(A - M X) = det(B - X M) for every real square matrix X. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory realTheory;

val putnam_2015_a6 =
  ``let matrix_eq =
      \n : num. \A B : num -> num -> real.
        !i j : num.
          i < n /\ j < n
          ==>
          A i j = B i j
    in
    let matrix_mul =
      \n : num. \A B : num -> num -> real. \i j : num.
        ITSET
          (\k : num. \sum : real. A i k * B k j + sum)
          (count n)
          0
    in
    let matrix_sub =
      \A B : num -> num -> real. \i j : num. A i j - B i j
    in
    let determinant =
      \n : num. \A : num -> num -> real.
        ITSET
          (\p : num -> num. \sum : real.
             (if evenperm p then
                ITSET
                  (\i : num. \acc : real. A i (p i) * acc)
                  (count n)
                  1
              else
                -(ITSET
                    (\i : num. \acc : real. A i (p i) * acc)
                    (count n)
                    1)) +
             sum)
          {p : num -> num | p permutes count n}
          0
    in
    let charpoly_eval =
      \n : num. \A : num -> num -> real. \t : real.
        determinant n
          (\i j : num. (if i = j then t else 0) - A i j)
    in
      !n : num. !A B M : num -> num -> real.
        0 < n /\
        matrix_eq n (matrix_mul n A M) (matrix_mul n M B) /\
        charpoly_eval n A = charpoly_eval n B
        ==>
        !X : num -> num -> real.
          determinant n (matrix_sub A (matrix_mul n M X)) =
          determinant n (matrix_sub B (matrix_mul n X M))``;
