(*
  Statement-only formalization of PutnamBench artifact putnam_1973_a2:
  an eight-periodic signed harmonic series converges exactly when each
  period contains four positive and four negative signs.

  The term with index i uses EL ((i - 1) MOD 8) L, so terms 1 and 9 have
  the same sign as in the published problem. This is a cyclic reindexing
  of the upstream Lean encoding and does not change the balance criterion.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_1973_a2 =
  ``!L : real list.
      LENGTH L = 8 /\
      (!i : num.
         i < LENGTH L
         ==>
         EL i L = (1 : real) \/ EL i L = ~(1 : real))
      ==>
      ((CARD {i : num | i < LENGTH L /\ EL i L = (1 : real)} = 4)
       <=>
       ?l : real.
         ((\n : num.
             SIGMA
               (\i : num. EL ((i - 1) MOD 8) L / &i)
               (IMAGE SUC (count n))) --> l)
           sequentially)``;
