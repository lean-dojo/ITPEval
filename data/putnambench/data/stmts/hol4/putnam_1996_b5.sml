(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_b5:
  the number of length-n two-symbol strings whose every consecutive substring
  has symbol-count imbalance at most two. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1996_b5 =
  ``!n : num.
      let balanced =
        \s : num -> bool.
          !a b : num.
            a < n /\ b < n /\ a <= b
            ==>
            (CARD {i : num | a <= i /\ i <= b /\ s i} <=
               CARD {i : num | a <= i /\ i <= b /\ ~s i} + 2 /\
             CARD {i : num | a <= i /\ i <= b /\ ~s i} <=
               CARD {i : num | a <= i /\ i <= b /\ s i} + 2)
      in
        CARD
          {s : num -> bool |
             (!i : num. n <= i ==> ~s i) /\ balanced s} =
        2 EXP ((n + 2) DIV 2) + 2 EXP ((n + 1) DIV 2) - 2``;
