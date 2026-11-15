(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_a1:
  the classification of positive integer pairs whose reciprocal sum is
  3/2018 into six explicit ordered pairs. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory ratTheory;

val putnam_2018_a1 =
  ``!a b : int.
      0 < a /\ 0 < b
      ==>
      ((1q / rat_of_int a + 1q / rat_of_int b =
        3q / rat_of_num 2018)
       <=>
       (a = 673 /\ b = 1358114) \/
       (a = 674 /\ b = 340033) \/
       (a = 1009 /\ b = 2018) \/
       (a = 2018 /\ b = 1009) \/
       (a = 340033 /\ b = 674) \/
       (a = 1358114 /\ b = 673))``;
