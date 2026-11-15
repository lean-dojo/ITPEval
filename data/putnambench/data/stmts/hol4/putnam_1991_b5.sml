(*
  Statement-only formalization of PutnamBench artifact putnam_1991_b5:
  the number of residue classes modulo an odd prime that are both a square
  and one more than a square. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1991_b5 =
  ``!p : num.
      ODD p /\ prime p
      ==>
      CARD
        ({z : num |
            z < p /\
            ?x : num. x < p /\ z = (x EXP 2) MOD p}
         INTER
         {z : num |
            z < p /\
            ?y : num. y < p /\ z = (y EXP 2 + 1) MOD p}) =
      p DIV 4 + 1``;
