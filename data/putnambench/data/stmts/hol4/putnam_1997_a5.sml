(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_a5:
  the number of ordered 10-tuples of positive integers whose reciprocals sum
  to one is odd. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_1997_a5 =
  ``ODD
      (CARD
        {a : num list |
           LENGTH a = 10 /\
           (!i : num. i < 10 ==> 0 < EL i a) /\
           SIGMA
             (\i : num. (1 : real) / &(EL i a))
             (count 10) =
           1})
    <=> T``;
