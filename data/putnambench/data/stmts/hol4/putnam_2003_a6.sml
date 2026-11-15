(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_a6:
  an affirmative answer to whether the nonnegative integers can be partitioned
  into two sets with equal counts of ordered distinct-element representations
  of every sum. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory;

val putnam_2003_a6 =
  ``let r =
      \S : num set. \n : num.
        CARD
          {p : num # num |
             FST p IN S /\
             SND p IN S /\
             FST p <> SND p /\
             FST p + SND p = n}
    in
    let putnam_2003_a6_solution = T
    in
      ((?A B : num set.
          A UNION B = UNIV /\
          A INTER B = EMPTY /\
          !n : num. r A n = r B n)
       <=>
       putnam_2003_a6_solution)``;
