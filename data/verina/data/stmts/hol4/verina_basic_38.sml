(*
  Statement-only formalization of VERINA corpus artifact verina_basic_38,
  catalog title "allCharactersSame": the executable Unicode-string test
  returns true exactly when all characters are identical, including for empty
  and singleton strings, and states its two-direction correctness contract.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val allCharactersSame_isUnicodeScalar_def = new_definition (
  "allCharactersSame_isUnicodeScalar_def",
  ``allCharactersSame_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val allCharactersSame_isUnicodeString_def = new_definition (
  "allCharactersSame_isUnicodeString_def",
  ``allCharactersSame_isUnicodeString (s : num list) <=>
      EVERY allCharactersSame_isUnicodeScalar s``
);

val allCharactersSame_precond_def = new_definition (
  "allCharactersSame_precond_def",
  ``allCharactersSame_precond (s : num list) <=> T``
);

val allCharactersSame_def = Define `
  (allCharactersSame ([] : num list) = T) /\
  (allCharactersSame (c::cs) =
     EVERY (\x : num. x = c) cs)
`;

val allCharactersSame_pairwise_def = Define `
  (allCharactersSame_pairwise ([] : num list) = T) /\
  (allCharactersSame_pairwise (c::cs) =
     (EVERY (\x : num. x = c) cs /\
      allCharactersSame_pairwise cs))
`;

val allCharactersSame_anyDifferent_def = Define `
  (allCharactersSame_anyDifferent ([] : num list) = F) /\
  (allCharactersSame_anyDifferent (c::cs) =
     EXISTS (\x : num. x <> c) (c::cs))
`;

val allCharactersSame_postcond_def = new_definition (
  "allCharactersSame_postcond_def",
  ``allCharactersSame_postcond
      (s : num list) (result : bool) <=>
      (result ==> allCharactersSame_pairwise s) /\
      (~result ==>
       (s <> [] /\ allCharactersSame_anyDifferent s))``
);

val allCharactersSame_spec_satisfied =
  ``!s : num list.
      allCharactersSame_isUnicodeString s ==>
      allCharactersSame_precond s ==>
      allCharactersSame_postcond
        s (allCharactersSame s)``;
