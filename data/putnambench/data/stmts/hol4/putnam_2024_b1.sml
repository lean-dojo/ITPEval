(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_b1:
  the positive grid sizes and offsets admitting a nonattacking selection whose
  entries are exactly the integers from 1 through the grid size are precisely
  (2*l+1,l+1) for natural l. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2024_b1 =
  ``!n k : num.
      (0 < n /\
       0 < k /\
       ?f : num -> num.
         BIJ f (count n) (count n) /\
         IMAGE
           (\i : num.
              int_of_num (SUC i) +
              int_of_num (SUC (f i)) -
              int_of_num k)
           (count n) =
         {z : int | 1 <= z /\ z <= int_of_num n})
      <=>
      ?l : num. n = 2 * l + 1 /\ k = l + 1``;
