(*
  Statement-only formalization of VERINA corpus artifact verina_basic_31,
  catalog title "toUppercase": the executable Unicode-string map converts
  ASCII lowercase letters to uppercase using the source's subtract-32 modulo
  128 transformation, leaves every other character unchanged, and states its
  length and pointwise correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val toUppercase_isUnicodeScalar_def = new_definition (
  "toUppercase_isUnicodeScalar_def",
  ``toUppercase_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val toUppercase_isUnicodeString_def = new_definition (
  "toUppercase_isUnicodeString_def",
  ``toUppercase_isUnicodeString (s : num list) <=>
      EVERY toUppercase_isUnicodeScalar s``
);

val isLowerCase_def = new_definition (
  "isLowerCase_def",
  ``isLowerCase (c : num) <=> 97 <= c /\ c <= 122``
);

val shiftMinus32_def = new_definition (
  "shiftMinus32_def",
  ``shiftMinus32 (c : num) = (c - 32) MOD 128``
);

val toUppercase_precond_def = new_definition (
  "toUppercase_precond_def",
  ``toUppercase_precond (s : num list) <=> T``
);

val toUppercase_def = new_definition (
  "toUppercase_def",
  ``toUppercase (s : num list) =
      MAP
        (\c : num. if isLowerCase c then shiftMinus32 c else c)
        s``
);

val toUppercase_postcond_def = new_definition (
  "toUppercase_postcond_def",
  ``toUppercase_postcond
      (s : num list) (result : num list) <=>
      LENGTH result = LENGTH s /\
      (!i : num.
         i < LENGTH s ==>
         (isLowerCase (EL i s) ==>
          EL i result = shiftMinus32 (EL i s)) /\
         (~isLowerCase (EL i s) ==>
          EL i result = EL i s))``
);

val toUppercase_spec_satisfied =
  ``!s : num list.
      toUppercase_isUnicodeString s ==>
      toUppercase_precond s ==>
      toUppercase_postcond s (toUppercase s)``;
