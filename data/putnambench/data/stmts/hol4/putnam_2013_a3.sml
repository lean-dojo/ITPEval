(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_a3:
  a vanishing real sum weighted by reciprocals of 1 - x^(i+1) yields a root
  in the open unit interval of the corresponding finite polynomial. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_2013_a3 =
  ``!n : num. !a : num -> real. !x : real.
      0 < x /\ x < 1 /\
      SIGMA
        (\i : num. a i / (1 - x pow (i + 1)))
        (count (SUC n)) = 0
      ==>
      ?y : real.
        0 < y /\ y < 1 /\
        SIGMA
          (\i : num. a i * y pow i)
          (count (SUC n)) = 0``;
