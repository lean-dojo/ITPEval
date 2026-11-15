(*
  Statement-only formalization of VERINA artifact verina_advanced_64,
  cataloged as "removeElement": the executable recursive program removes every
  occurrence of a target natural number from a list while preserving the order
  of all remaining elements. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory optionTheory pairTheory;

val removeElement_precond_def = new_definition (
  "removeElement_precond_def",
  ``removeElement_precond (lst : num list) (target : num) <=> T``
);

val removeElement_helper_def = Define `
  (removeElement_helper ([] : num list) (target : num) = []) /\
  (removeElement_helper (x::xs) target =
     let rest = removeElement_helper xs target
     in
       if x = target then rest else x::rest)
`;

val removeElement_def = new_definition (
  "removeElement_def",
  ``removeElement (lst : num list) (target : num) =
      removeElement_helper lst target``
);

val removeElement_zipIdxFrom_def = Define `
  (removeElement_zipIdxFrom
      (index : num)
      ([] : num list) =
     ([] : (num # num) list)) /\
  (removeElement_zipIdxFrom
      index
      (x::xs) =
     (x,index)::removeElement_zipIdxFrom (SUC index) xs)
`;

val removeElement_zipIdx_def = new_definition (
  "removeElement_zipIdx_def",
  ``removeElement_zipIdx (xs : num list) =
      removeElement_zipIdxFrom 0 xs``
);

val removeElement_getOpt_def = new_definition (
  "removeElement_getOpt_def",
  ``removeElement_getOpt
      (xs : num list) (index : num) =
      if index < LENGTH xs then
        SOME (EL index xs)
      else
        (NONE : num option)``
);

val removeElement_postcond_def = new_definition (
  "removeElement_postcond_def",
  ``removeElement_postcond
      (lst : num list)
      (target : num)
      (result : num list) <=>
      let filtered =
        FILTER (\x : num. ~(x = target)) lst
      in
        EVERY
          (\entry : num # num.
             case removeElement_getOpt filtered (SND entry) of
               NONE => F
             | SOME y => FST entry = y)
          (removeElement_zipIdx result) /\
        LENGTH result = LENGTH filtered``
);

val removeElement_spec_satisfied =
  ``!(lst : num list) (target : num).
      removeElement_precond lst target ==>
      removeElement_postcond
        lst target (removeElement lst target)``;
