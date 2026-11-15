(*
  Statement-only formalization of "Ramsey's Theorem" from Hundred Theorems item 031. This file
  contains no proof.
*)

(*
  Hundred Theorems item 031, "Ramsey's Theorem": every finite coloring of the
  fixed-cardinality finite subsets of an infinite set has an infinite
  homogeneous subset. This is a statement-only formalization and contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val ramsey_s_theorem =
  ``!M N (C : 'a set -> num) (s : 'a set).
      INFINITE s /\
      (!X : 'a set.
         X SUBSET s /\ FINITE X /\ CARD X = N ==>
         C X <= M)
      ==>
      ?t c.
        INFINITE t /\
        t SUBSET s /\
        c <= M /\
        (!X : 'a set.
           X SUBSET t /\ FINITE X /\ CARD X = N ==>
           C X = c)``;
