(*
  Statement-only formalization of VERINA corpus artifact verina_basic_41,
  catalog title "hasOnlyOneDistinctElement": the executable integer-array
  scan returns true exactly when all entries equal the first entry, under the
  nonempty-array precondition, and satisfies the stated two-branch correctness
  contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val hasOnlyOneDistinctElement_precond_def = new_definition (
  "hasOnlyOneDistinctElement_precond_def",
  ``hasOnlyOneDistinctElement_precond (a : int list) <=>
      0 < LENGTH a``
);

val hasOnlyOneDistinctElement_def = Define `
  (hasOnlyOneDistinctElement ([] : int list) = T) /\
  (hasOnlyOneDistinctElement (first::rest) =
     EVERY (\x : int. x = first) rest)
`;

val hasOnlyOneDistinctElement_pairwise_def = Define `
  (hasOnlyOneDistinctElement_pairwise ([] : int list) = T) /\
  (hasOnlyOneDistinctElement_pairwise (first::rest) =
     (EVERY (\x : int. x = first) rest /\
      hasOnlyOneDistinctElement_pairwise rest))
`;

val hasOnlyOneDistinctElement_anyDifferent_def = Define `
  (hasOnlyOneDistinctElement_anyDifferent ([] : int list) = F) /\
  (hasOnlyOneDistinctElement_anyDifferent (first::rest) =
     EXISTS (\x : int. x <> first) (first::rest))
`;

val hasOnlyOneDistinctElement_postcond_def = new_definition (
  "hasOnlyOneDistinctElement_postcond_def",
  ``hasOnlyOneDistinctElement_postcond
      (a : int list) (result : bool) <=>
      (result ==> hasOnlyOneDistinctElement_pairwise a) /\
      (~result ==> hasOnlyOneDistinctElement_anyDifferent a)``
);

val hasOnlyOneDistinctElement_spec_satisfied =
  ``!a : int list.
      hasOnlyOneDistinctElement_precond a ==>
      hasOnlyOneDistinctElement_postcond
        a (hasOnlyOneDistinctElement a)``;
