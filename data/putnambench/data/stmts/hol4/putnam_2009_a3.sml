(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_a3:
  the determinants of the row-major n by n cosine matrices converge to zero
  as n tends to infinity. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory realTheory;
open real_topologyTheory transcTheory;

val putnam_2009_a3 =
  ``let determinant =
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
      !cos_matrix : num -> num -> num -> real.
        (!n i j : num.
           i < n /\ j < n
           ==>
           cos_matrix n i j = cos (&(1 + n * i + j)))
        ==>
        ((\n : num. determinant n (cos_matrix n)) --> (0 : real))
          sequentially``;
