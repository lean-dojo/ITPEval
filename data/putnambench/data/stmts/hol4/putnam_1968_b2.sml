(*
  Statement-only formalization of PutnamBench artifact putnam_1968_b2:
  every element of a finite group is a product of two elements of any subset
  containing more than half of the group. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory groupTheory;

val putnam_1968_b2 =
  ``!(g : 'a group) (A : 'a set).
      FiniteGroup g /\
      A SUBSET g.carrier /\
      CARD A > CARD g.carrier DIV 2
      ==>
      !z : 'a.
        z IN g.carrier
        ==>
        ?x y : 'a.
          x IN A /\ y IN A /\ z = g.op x y``;
