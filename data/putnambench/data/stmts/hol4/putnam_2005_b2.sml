(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_b2:
  the classification of positive integer tuples whose sum is five times
  their length minus four and whose reciprocal sum is one. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory
     real_sigmaTheory;

val putnam_2005_b2 =
  ``!n : num. !k : num -> int.
      (0 < n /\
       (!i : num. i < n ==> 0 < k i) /\
       SIGMA k (count n) = int_of_num (5 * n) - 4 /\
       SIGMA
         (\i : num. (1 : real) / real_of_int (k i))
         (count n) =
         1)
      <=>
      (n = 1 /\ k 0 = 1) \/
      (n = 3 /\
       ((k 0 = 2 /\ k 1 = 3 /\ k 2 = 6) \/
        (k 0 = 2 /\ k 1 = 6 /\ k 2 = 3) \/
        (k 0 = 3 /\ k 1 = 2 /\ k 2 = 6) \/
        (k 0 = 3 /\ k 1 = 6 /\ k 2 = 2) \/
        (k 0 = 6 /\ k 1 = 2 /\ k 2 = 3) \/
        (k 0 = 6 /\ k 1 = 3 /\ k 2 = 2))) \/
      (n = 4 /\ k 0 = 4 /\ k 1 = 4 /\ k 2 = 4 /\ k 3 = 4)``;
