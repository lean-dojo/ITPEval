(*
  Statement-only formalization of PutnamBench artifact putnam_1966_b4:
  a finite set of mn + 1 positive natural numbers contains either an
  (m + 1)-element divisibility antichain or an (n + 1)-element divisibility
  chain. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val putnam_1966_b4 =
  ``!m n : num. !S : num set.
      FINITE S /\
      CARD S = m * n + 1 /\
      (!i : num. i IN S ==> 0 < i)
      ==>
      ?T : num set.
        T SUBSET S /\
        FINITE T /\
        ((CARD T = m + 1 /\
          !j i : num.
            j IN T /\ i IN T /\ i <> j
            ==>
            ~(divides j i)) \/
         (CARD T = n + 1 /\
          !j i : num.
            j IN T /\ i IN T /\ j < i
            ==>
            divides j i))``;
