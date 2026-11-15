(*
  Statement-only formalization of VERINA artifact verina_advanced_65,
  cataloged as "reverseString": the executable tail-recursive program reverses
  the Unicode scalar values of a string and returns the exact character-list
  reversal with unchanged length. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val reverseString_isUnicodeScalar_def = new_definition (
  "reverseString_isUnicodeScalar_def",
  ``reverseString_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val reverseString_isUnicodeString_def = new_definition (
  "reverseString_isUnicodeString_def",
  ``reverseString_isUnicodeString (s : num list) <=>
      EVERY reverseString_isUnicodeScalar s``
);

val reverseString_precond_def = new_definition (
  "reverseString_precond_def",
  ``reverseString_precond (s : num list) <=> T``
);

val reverseString_reverseAux_def = Define `
  (reverseString_reverseAux
      ([] : num list) (acc : num list) = acc) /\
  (reverseString_reverseAux
      (h::t) acc =
     reverseString_reverseAux t (h::acc))
`;

val reverseString_def = new_definition (
  "reverseString_def",
  ``reverseString (s : num list) =
      reverseString_reverseAux s ([] : num list)``
);

val reverseString_postcond_def = new_definition (
  "reverseString_postcond_def",
  ``reverseString_postcond
      (s : num list) (result : num list) <=>
      LENGTH result = LENGTH s /\
      result = REVERSE s``
);

val reverseString_spec_satisfied =
  ``!s : num list.
      reverseString_isUnicodeString s ==>
      reverseString_precond s ==>
      reverseString_postcond s (reverseString s)``;
