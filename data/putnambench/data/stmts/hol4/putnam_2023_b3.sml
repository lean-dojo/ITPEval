(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_b3:
  the expected length of the longest zigzag subsequence of independent
  uniform unit-interval random variables is (2n + 2) / 3 for n at least 2.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory;
open extrealTheory measureTheory borelTheory lebesgue_measureTheory
     probabilityTheory;

val putnam_2023_b3 =
  ``let zigzag =
      \k : num. \y : num -> real.
        0 < k /\
        (k = 1 \/
         ((!i : num.
             i + 1 < k
             ==>
             y (i + 1) <> y i) /\
          (!i : num.
             i + 2 < k
             ==>
             (y (i + 2) < y (i + 1) <=>
              y i < y (i + 1)))))
    in
    let is_zigzag_subsequence =
      \n : num. \X : num -> 'a -> real. \w : 'a. \k : num.
        ?idx : num -> num.
          (!j : num. j < k ==> idx j < n) /\
          (!j : num.
             j + 1 < k
             ==>
             idx j < idx (j + 1)) /\
          zigzag k (\j : num. X (idx j) w)
    in
      !n : num.
      !(p : 'a p_space) (X : num -> 'a -> real) (a : 'a -> num).
        2 <= n /\
        prob_space p /\
        (!i : num.
           i < n
           ==>
           random_variable (X i) p Borel) /\
        (!i : num. !s : real set.
           i < n /\ s IN subsets Borel
           ==>
           distribution p (X i) s =
             measure lborel (s INTER interval [0, 1])) /\
        indep_vars p X (\i : num. Borel) (count n) /\
        (!w : 'a.
           w IN p_space p
           ==>
           is_zigzag_subsequence n X w (a w) /\
           (!k : num.
              is_zigzag_subsequence n X w k
              ==>
              k <= a w))
        ==>
        expectation p (\w : 'a. Normal (&(a w))) =
          Normal ((2 * &n + 2) / 3)``;
