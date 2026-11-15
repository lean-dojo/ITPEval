(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_b3:
  a sufficiently large set of 2 by 2 natural-number matrices with bounded
  square entries contains two distinct commuting matrices. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory fcpTheory;

val putnam_1990_b3 =
  ``!S : num['N]['N] set.
      dimindex (:'N) = 2 /\
      (!A : num['N]['N].
         A IN S
         ==>
         !i j : num.
           i < 2 /\ j < 2
           ==>
           (?x : num. A ' i ' j = x EXP 2) /\
           A ' i ' j <= 200)
      ==>
      50387 < CARD S
      ==>
      ?A : num['N]['N].
        A IN S /\
        ?B : num['N]['N].
          B IN S /\
          A <> B /\
          ((FCP i j.
              SIGMA
                (\k : num. A ' i ' k * B ' k ' j)
                (count 2)) : num['N]['N]) =
          ((FCP i j.
              SIGMA
                (\k : num. B ' i ' k * A ' k ' j)
                (count 2)) : num['N]['N])``;
