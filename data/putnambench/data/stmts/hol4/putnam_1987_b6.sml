(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_b6:
  a half-set of the nonzero elements of a field of odd prime-square order
  meets its additive double in an even number of elements. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory groupTheory ringTheory;

val putnam_1987_b6 =
  ``!(p : num) (r : 'a ring) (S : 'a set).
      ODD p /\
      prime p /\
      Ring r /\
      Group (r.prod excluding r.sum.id) /\
      FINITE r.carrier /\
      CARD r.carrier = p EXP 2 /\
      S SUBSET r.carrier /\
      (!x : 'a. x IN S ==> x <> r.sum.id) /\
      CARD S = (p EXP 2 - 1) DIV 2 /\
      (!a : 'a.
         a IN r.carrier /\ a <> r.sum.id
         ==>
         ~((a IN S) <=> (r.sum.inv a IN S)))
      ==>
      EVEN
        (CARD
           (S INTER
            {x : 'a |
               x IN r.carrier /\
               ?a : 'a. a IN S /\ x = r.sum.op a a}))``;
