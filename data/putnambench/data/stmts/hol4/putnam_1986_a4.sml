(*
  Statement-only formalization of PutnamBench artifact putnam_1986_a4:
  the number of n by n matrices with entries in {-1, 0, 1} whose
  transversal sums are all equal has the specified rational-exponential
  formula for every positive n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory ratTheory;

val putnam_1986_a4 =
  ``!f : num -> num.
      (!n : num.
         f n =
           CARD
             {A : num -> num -> int |
                (!i j : num.
                   i < n /\ j < n
                   ==>
                   (A i j = ~1 \/ A i j = 0 \/ A i j = 1)) /\
                (!i j : num.
                   n <= i \/ n <= j
                   ==>
                   A i j = 0) /\
                (?S : int.
                   !p : num -> num.
                     BIJ p (count n) (count n)
                     ==>
                     ITSET
                       (\i : num. \acc : int. A i (p i) + acc)
                       (count n)
                       0 = S)})
      ==>
      !n : num.
        0 < n
        ==>
        rat_of_num (f n) =
          1q * rat_expn 4q n +
          2q * rat_expn 3q n +
          ~4q * rat_expn 2q n +
          1q``;
