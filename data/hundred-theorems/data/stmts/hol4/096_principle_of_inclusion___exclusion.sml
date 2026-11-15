(*
  Statement-only formalization of Hundred Theorems artifact
  hundred-theorems__hol4__096, cataloged as "Principle of Inclusion / Exclusion":
  the cardinality of a finite indexed union of finite sets is the alternating
  integer sum of the cardinalities of all nonempty indexed subfamily
  intersections. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val principle_of_inclusion_exclusion =
  ``!A : 'i set. !x : 'i -> 'a set.
      FINITE A /\ (!i. i IN A ==> FINITE (x i)) ==>
      &(CARD (BIGUNION (IMAGE x A))) =
        SIGMA
          (\B.
             (~1 : int) ** (CARD B + 1) *
             &(CARD (BIGINTER (IMAGE x B))))
          {B | B SUBSET A /\ B <> {}}``;
