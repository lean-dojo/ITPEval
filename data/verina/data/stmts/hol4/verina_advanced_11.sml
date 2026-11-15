(*
  Statement-only formalization of VERINA artifact verina_advanced_11,
  cataloged as "findMajorityElement": the program returns the first integer
  occurring strictly more than half the list length, or -1 if none exists.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val findMajorityElement_precond_def = new_definition (
  "findMajorityElement_precond_def",
  ``findMajorityElement_precond (lst : int list) <=> T``
);

val countOccurrences_def = new_definition (
  "countOccurrences_def",
  ``countOccurrences (n : int) (lst : int list) =
      FOLDL
        (\acc x. if x = n then acc + 1 else acc)
        0
        lst``
);

val findMajorityCandidate_def = Define `
  (findMajorityCandidate (lst : int list) ([] : int list) =
     (NONE : int option)) /\
  (findMajorityCandidate lst (x::xs) =
     if countOccurrences x lst > LENGTH lst DIV 2 then
       SOME x
     else
       findMajorityCandidate lst xs)
`;

val findMajorityElement_def = new_definition (
  "findMajorityElement_def",
  ``findMajorityElement (lst : int list) =
      case findMajorityCandidate lst lst of
        NONE => (~1 : int)
      | SOME x => x``
);

val findMajorityElement_postcond_def = new_definition (
  "findMajorityElement_postcond_def",
  ``findMajorityElement_postcond
      (lst : int list) (result : int) <=>
      let count =
        \x : int. LENGTH (FILTER (\y : int. y = x) lst)
      in
      let n = LENGTH lst
      in
      let majority =
        count result > n DIV 2 /\
        EVERY (\x : int. count x <= n DIV 2 \/ x = result) lst
      in
        (result = (~1 : int) ==>
          EVERY (\x : int. count x <= n DIV 2) lst \/ majority) /\
        (result <> (~1 : int) ==> majority)``
);

val findMajorityElement_spec_satisfied =
  ``!lst : int list.
      findMajorityElement_precond lst ==>
      findMajorityElement_postcond lst (findMajorityElement lst)``;
