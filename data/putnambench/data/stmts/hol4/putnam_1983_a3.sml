(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_a3:
  the polynomial with coefficients 1 through p - 1 takes pairwise
  incongruent values modulo an odd prime p on the residues below p. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1983_a3 =
  ``!p : num. !F : num -> num.
      ODD p /\ prime p /\
      (!n : num.
         F n =
         SIGMA
           (\i : num. (i + 1) * n EXP i)
           (count (p - 1)))
      ==>
      !a b : num.
        a < p /\ b < p /\ a <> b
        ==>
        F a MOD p <> F b MOD p``;
