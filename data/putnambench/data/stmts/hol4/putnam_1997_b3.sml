(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_b3:
  the positive integers whose harmonic sum has reduced denominator not
  divisible by 5 are exactly four specified intervals. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory ratTheory;

val putnam_1997_b3 =
  ``!n : num.
      0 < n
      ==>
      (((1 <= n /\ n <= 4) \/
        (20 <= n /\ n <= 24) \/
        (100 <= n /\ n <= 104) \/
        (120 <= n /\ n <= 124)) <=>
       ~divides 5
         (RATD
           (ITSET
             (\m : num. \acc : rat.
                rat_add (1q / rat_of_num m) acc)
             {m : num | 1 <= m /\ m <= n}
             0q)))``;
