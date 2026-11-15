(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_b3:
  a valuation on a nonempty lattice of subsets with one-element descent is
  representable as a sum of real weights. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_2013_b3 =
  ``!n : num.
      !(P : num set set) (f : num set -> real).
        P <> {} /\
        (!S : num set.
           S IN P
           ==>
           S SUBSET count n) /\
        (!S T : num set.
           S IN P /\ T IN P
           ==>
           S UNION T IN P /\ S INTER T IN P) /\
        (!S : num set.
           S IN P /\ S <> {}
           ==>
           ?T : num set.
             T IN P /\
             T PSUBSET S /\
             CARD T + 1 = CARD S) /\
        f {} = 0 /\
        (!S T : num set.
           S IN P /\ T IN P
           ==>
           f (S UNION T) = f S + f T - f (S INTER T))
        ==>
        ?r : num -> real.
          !S : num set.
            S IN P
            ==>
            f S = SIGMA r S``;
