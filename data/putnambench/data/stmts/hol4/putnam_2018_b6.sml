(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_b6:
  the number of length-2018 sequences with terms in {1,2,3,4,5,6,10} and
  sum 3860 is at most the stated exponential real bound. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory;

val putnam_2018_b6 =
  ``(&(CARD
        {xs : num list |
           LENGTH xs = 2018 /\
           (!x : num.
              MEM x xs ==>
              (x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/
               x = 5 \/ x = 6 \/ x = 10)) /\
           SUM xs = 3860}) : real) <=
    (2 : real) pow 3860 * ((2018 : real) / 2048) pow 2018``;
