(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_b3:
  redistribution among 2010 labeled boxes by moving the source box's label
  number of balls reaches the uniform distribution for every initial
  distribution exactly when the positive integer n is at least 1005.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_2010_b3 =
  ``!n : num.
      0 < n
      ==>
      ((!B : num -> num.
          SIGMA B (count 2010) = 2010 * n
          ==>
          ?P : num -> num -> num.
          ?T : num.
            (!i : num. i < 2010 ==> P 0 i = B i) /\
            (!t : num.
               t < T
               ==>
               ?i j : num.
                 i < 2010 /\
                 j < 2010 /\
                 i <> j /\
                 i + 1 <= P t i /\
                 P (t + 1) i = P t i - (i + 1) /\
                 P (t + 1) j = P t j + (i + 1) /\
                 !k : num.
                   k < 2010 /\ k <> i /\ k <> j
                   ==>
                   P (t + 1) k = P t k) /\
            !i : num. i < 2010 ==> P T i = n)
       <=>
       1005 <= n)``;
