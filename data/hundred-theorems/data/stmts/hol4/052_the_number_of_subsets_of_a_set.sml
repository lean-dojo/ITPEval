(*
  Statement-only formalization of "The Number of Subsets of a Set" from Hundred Theorems
  item 052. For every finite set, the cardinality of its powerset is two raised to the
  cardinality of the set. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val number_of_subsets_of_a_set =
  ``!s : 'a set.
      FINITE s ==>
      CARD (POW s) = 2 EXP (CARD s)``;
