(*
  Statement-only formalization of VERINA corpus artifact verina_basic_42,
  catalog title "countDigits": the executable natural-number program counts
  ASCII digit characters in a Unicode-scalar string and satisfies the exact
  filter-length correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val countDigits_isUnicodeScalar_def = new_definition (
  "countDigits_isUnicodeScalar_def",
  ``countDigits_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val countDigits_isUnicodeString_def = new_definition (
  "countDigits_isUnicodeString_def",
  ``countDigits_isUnicodeString (s : num list) <=>
      EVERY countDigits_isUnicodeScalar s``
);

val countDigits_isDigit_def = new_definition (
  "countDigits_isDigit_def",
  ``countDigits_isDigit (c : num) <=>
      48 <= c /\ c <= 57``
);

val countDigits_precond_def = new_definition (
  "countDigits_precond_def",
  ``countDigits_precond (s : num list) <=> T``
);

val countDigits_def = new_definition (
  "countDigits_def",
  ``countDigits (s : num list) =
      LENGTH (FILTER countDigits_isDigit s)``
);

val countDigits_postcond_def = new_definition (
  "countDigits_postcond_def",
  ``countDigits_postcond (s : num list) (result : num) <=>
      result - LENGTH (FILTER countDigits_isDigit s) = 0 /\
      LENGTH (FILTER countDigits_isDigit s) - result = 0``
);

val countDigits_spec_satisfied =
  ``!s : num list.
      countDigits_isUnicodeString s ==>
      countDigits_precond s ==>
      countDigits_postcond s (countDigits s)``;
