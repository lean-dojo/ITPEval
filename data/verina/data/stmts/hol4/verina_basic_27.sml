(*
  Statement-only formalization of VERINA corpus artifact verina_basic_27,
  catalog title "findFirstRepeatedChar": the executable Unicode-string scan
  returns the character whose second occurrence is encountered first, or NONE
  when all characters are distinct, together with its complete correctness
  contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory optionTheory;

val findFirstRepeatedChar_isUnicodeScalar_def = new_definition (
  "findFirstRepeatedChar_isUnicodeScalar_def",
  ``findFirstRepeatedChar_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val findFirstRepeatedChar_isUnicodeString_def = new_definition (
  "findFirstRepeatedChar_isUnicodeString_def",
  ``findFirstRepeatedChar_isUnicodeString (s : num list) <=>
      EVERY findFirstRepeatedChar_isUnicodeScalar s``
);

val findFirstRepeatedChar_precond_def = new_definition (
  "findFirstRepeatedChar_precond_def",
  ``findFirstRepeatedChar_precond (s : num list) <=> T``
);

val findFirstRepeatedChar_loop_def = Define `
  (findFirstRepeatedChar_loop
      ([] : num list) (seen : num list) =
     (NONE : num option)) /\
  (findFirstRepeatedChar_loop
      (c::cs) seen =
     if MEM c seen then
       SOME c
     else
       findFirstRepeatedChar_loop cs (c::seen))
`;

val findFirstRepeatedChar_def = new_definition (
  "findFirstRepeatedChar_def",
  ``findFirstRepeatedChar (s : num list) =
      findFirstRepeatedChar_loop s ([] : num list)``
);

val findFirstRepeatedChar_count_def = Define `
  (findFirstRepeatedChar_count
      (target : num) ([] : num list) = 0) /\
  (findFirstRepeatedChar_count
      target (c::cs) =
     if c = target then
       SUC (findFirstRepeatedChar_count target cs)
     else
       findFirstRepeatedChar_count target cs)
`;

val findFirstRepeatedChar_idxOf_def = Define `
  (findFirstRepeatedChar_idxOf
      (target : num) ([] : num list) = 0) /\
  (findFirstRepeatedChar_idxOf
      target (c::cs) =
     if c = target then
       0
     else
       SUC (findFirstRepeatedChar_idxOf target cs))
`;

val findFirstRepeatedChar_secondIndexFrom_def = Define `
  (findFirstRepeatedChar_secondIndexFrom
      (target : num)
      (firstIndex : num)
      (currentIndex : num)
      ([] : num list) =
     currentIndex) /\
  (findFirstRepeatedChar_secondIndexFrom
      target firstIndex currentIndex (c::cs) =
     if c = target /\ currentIndex <> firstIndex then
       currentIndex
     else
       findFirstRepeatedChar_secondIndexFrom
         target firstIndex (SUC currentIndex) cs)
`;

val findFirstRepeatedChar_secondIndex_def = new_definition (
  "findFirstRepeatedChar_secondIndex_def",
  ``findFirstRepeatedChar_secondIndex
      (target : num) (s : num list) =
      findFirstRepeatedChar_secondIndexFrom
        target (findFirstRepeatedChar_idxOf target s) 0 s``
);

val findFirstRepeatedChar_pairwiseDistinct_def = Define `
  (findFirstRepeatedChar_pairwiseDistinct ([] : num list) = T) /\
  (findFirstRepeatedChar_pairwiseDistinct (c::cs) =
     (EVERY (\later : num. c <> later) cs /\
      findFirstRepeatedChar_pairwiseDistinct cs))
`;

val findFirstRepeatedChar_postcond_def = new_definition (
  "findFirstRepeatedChar_postcond_def",
  ``findFirstRepeatedChar_postcond
      (s : num list) (result : num option) <=>
      case result of
        NONE =>
          findFirstRepeatedChar_pairwiseDistinct s
      | SOME c =>
          findFirstRepeatedChar_count c s >= 2 /\
          findFirstRepeatedChar_pairwiseDistinct
            (TAKE (findFirstRepeatedChar_secondIndex c s) s)``
);

val findFirstRepeatedChar_spec_satisfied =
  ``!s : num list.
      findFirstRepeatedChar_isUnicodeString s ==>
      findFirstRepeatedChar_precond s ==>
      findFirstRepeatedChar_postcond
        s (findFirstRepeatedChar s)``;
