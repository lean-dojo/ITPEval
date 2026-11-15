(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_b2:
  repeated adjacent averaging of the rational sequence 1, 1/2, ..., 1/n
  yields a final value strictly less than 2/n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory ratTheory;

val putnam_2003_b2 =
  ``!n : num. !seq : num -> num -> rat.
      0 < n /\
      (!j : num.
         1 <= j /\ j <= n
         ==>
         seq 0 j = 1q / rat_of_num j) /\
      (!k : num.
         1 <= k /\ k <= n - 1
         ==>
         !j : num.
           1 <= j /\ j <= n - k
           ==>
           seq k j =
             (seq (k - 1) j + seq (k - 1) (j + 1)) / 2q)
      ==>
      seq (n - 1) 1 < 2q / rat_of_num n``;
