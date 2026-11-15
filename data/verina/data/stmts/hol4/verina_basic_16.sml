(*
  Statement-only formalization of VERINA corpus artifact verina_basic_16,
  catalog title "replaceChars": the executable Unicode-string map replaces
  every occurrence of one character with another while preserving length and
  all other characters. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val replaceChars_isUnicodeScalar_def = new_definition (
  "replaceChars_isUnicodeScalar_def",
  ``replaceChars_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val replaceChars_isUnicodeString_def = new_definition (
  "replaceChars_isUnicodeString_def",
  ``replaceChars_isUnicodeString (s : num list) <=>
      EVERY replaceChars_isUnicodeScalar s``
);

val replaceChars_precond_def = new_definition (
  "replaceChars_precond_def",
  ``replaceChars_precond
      (s : num list) (oldChar : num) (newChar : num) <=>
      T``
);

val replaceChars_def = new_definition (
  "replaceChars_def",
  ``replaceChars
      (s : num list) (oldChar : num) (newChar : num) =
      MAP
        (\c : num. if c = oldChar then newChar else c)
        s``
);

val replaceChars_postcond_def = new_definition (
  "replaceChars_postcond_def",
  ``replaceChars_postcond
      (s : num list)
      (oldChar : num)
      (newChar : num)
      (result : num list) <=>
      LENGTH result = LENGTH s /\
      (!i : num.
         i < LENGTH s ==>
         (EL i s = oldChar ==> EL i result = newChar) /\
         (EL i s <> oldChar ==> EL i result = EL i s))``
);

val replaceChars_spec_satisfied =
  ``!(s : num list) (oldChar : num) (newChar : num).
      replaceChars_isUnicodeString s ==>
      replaceChars_isUnicodeScalar oldChar ==>
      replaceChars_isUnicodeScalar newChar ==>
      replaceChars_precond s oldChar newChar ==>
      replaceChars_postcond
        s oldChar newChar (replaceChars s oldChar newChar)``;
