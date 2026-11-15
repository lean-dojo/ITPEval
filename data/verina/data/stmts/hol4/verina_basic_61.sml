(*
  Statement-only formalization of VERINA corpus artifact verina_basic_61,
  catalog title "allDigits": the executable Unicode-string program scans from
  left to right and returns true exactly when every character is an ASCII
  decimal digit from '0' through '9'. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val allDigits_isUnicodeScalar_def = new_definition (
  "allDigits_isUnicodeScalar_def",
  ``allDigits_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val allDigits_isUnicodeString_def = new_definition (
  "allDigits_isUnicodeString_def",
  ``allDigits_isUnicodeString (s : num list) <=>
      EVERY allDigits_isUnicodeScalar s``
);

val allDigits_isDigit_def = new_definition (
  "allDigits_isDigit_def",
  ``allDigits_isDigit (c : num) <=> 48 <= c /\ c <= 57``
);

val allDigits_precond_def = new_definition (
  "allDigits_precond_def",
  ``allDigits_precond (s : num list) <=> T``
);

val allDigits_loop_def = Define `
  (allDigits_loop ([] : num list) = T) /\
  (allDigits_loop (c::cs) =
     if ~allDigits_isDigit c then
       F
     else
       allDigits_loop cs)
`;

val allDigits_def = new_definition (
  "allDigits_def",
  ``allDigits (s : num list) = allDigits_loop s``
);

val allDigits_postcond_def = new_definition (
  "allDigits_postcond_def",
  ``allDigits_postcond
      (s : num list) (result : bool) <=>
      (result = T <=> EVERY allDigits_isDigit s)``
);

val allDigits_spec_satisfied =
  ``!s : num list.
      allDigits_isUnicodeString s ==>
      allDigits_precond s ==>
      allDigits_postcond s (allDigits s)``;
