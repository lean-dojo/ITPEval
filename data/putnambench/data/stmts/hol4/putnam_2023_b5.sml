(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_b5:
  the positive integers for which every coprime integer multiplier modulo n
  is the square of a permutation of the residues 1 through n are exactly 1
  and the integers congruent to 2 modulo 4. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory integerTheory pred_setTheory;

val putnam_2023_b5 =
  ``!n : num.
      (n = 1 \/ n MOD 4 = 2) <=>
      0 < n /\
      !m : int.
        gcd (Num (ABS m)) n = 1
        ==>
        ?p : num -> num.
          BIJ p (count n) (count n) /\
          !k : num.
            k < n
            ==>
            ?q : int.
              int_of_num (p (p k) + 1) =
                m * int_of_num (k + 1) + int_of_num n * q``;
