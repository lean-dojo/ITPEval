(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_a1:
  the largest number of equal-sum boxes into which the integers from 1 through
  a positive integer n can be partitioned. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory real_sigmaTheory;

val putnam_2010_a1 =
  ``!n : num. !kboxes : num -> bool.
      0 < n /\
      (!k : num.
         kboxes k <=>
         ?boxes : num -> num.
           (!m : num.
              m IN IMAGE SUC (count n)
              ==>
              boxes m < k) /\
           (!i j : num.
              i < k /\ j < k
              ==>
              SIGMA
                (\x : num. if boxes x = i then x else 0)
                (IMAGE SUC (count n)) =
              SIGMA
                (\x : num. if boxes x = j then x else 0)
                (IMAGE SUC (count n))))
      ==>
      kboxes ((n + 1) DIV 2) /\
      (!k : num. kboxes k ==> k <= (n + 1) DIV 2)``;
