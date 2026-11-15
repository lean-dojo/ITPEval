(*
  Statement-only formalization of PutnamBench artifact putnam_1971_a5:
  positive integer point values whose nonnegative combinations omit exactly
  35 scores, including 58, are characterized as 11 and 8. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory;

val putnam_1971_a5 =
  ``!a b : int.
      0 < a /\ 0 < b /\ b < a
      ==>
      ((FINITE
          {s : num |
             ~?m n : num.
               int_of_num m * a + int_of_num n * b = int_of_num s} /\
        CARD
          {s : num |
             ~?m n : num.
               int_of_num m * a + int_of_num n * b = int_of_num s} =
        35 /\
        ~?m n : num.
          int_of_num m * a + int_of_num n * b = 58)
       <=>
       a = 11 /\ b = 8)``;
