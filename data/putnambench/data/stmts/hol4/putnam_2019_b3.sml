(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_b3:
  a Householder reflection formed from a real unit vector makes the product
  with an orthogonal matrix have eigenvalue one when the original matrix does
  not. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory realTheory real_sigmaTheory;

val putnam_2019_b3 =
  ``let dot =
      \n : num. \x y : num -> real.
        SIGMA (\k : num. x k * y k) (count n)
    in
    let matrix_mul =
      \n : num. \A B : num -> num -> real. \i j : num.
        SIGMA (\k : num. A i k * B k j) (count n)
    in
    let identity =
      \i j : num. if i = j then 1 else 0
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
      !n : num. !Q : num -> num -> real. !u : num -> real.
        0 < n /\
        (!i j : num.
           i < n /\ j < n /\ i <> j
           ==>
           dot n (Q i) (Q j) = 0 /\
           dot n (\k. Q k i) (\k. Q k j) = 0) /\
        (!i : num.
           i < n
           ==>
           dot n (Q i) (Q i) = 1 /\
           dot n (\k. Q k i) (\k. Q k i) = 1) /\
        dot n u u = 1 /\
        determinant n (\i j. Q i j - identity i j) <> 0
        ==>
        determinant n
          (\i j.
             matrix_mul n
               (\r c. identity r c - 2 * u r * u c)
               Q i j -
             identity i j) =
        0``;
