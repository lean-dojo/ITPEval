(*
  Statement-only formalization of VERINA corpus artifact verina_basic_17,
  catalog title "toLowercase": the executable Unicode-string map converts
  ASCII uppercase letters to lowercase by adding 32 to their code points,
  leaves every other character unchanged, and states its length and pointwise
  correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val toLowercase_isUnicodeScalar_def = new_definition (
  "toLowercase_isUnicodeScalar_def",
  ``toLowercase_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val toLowercase_isUnicodeString_def = new_definition (
  "toLowercase_isUnicodeString_def",
  ``toLowercase_isUnicodeString (s : num list) <=>
      EVERY toLowercase_isUnicodeScalar s``
);

val isUpperCase_def = new_definition (
  "isUpperCase_def",
  ``isUpperCase (c : num) <=> 65 <= c /\ c <= 90``
);

val shift32_def = new_definition (
  "shift32_def",
  ``shift32 (c : num) =
      if toLowercase_isUnicodeScalar (c + 32) then c + 32 else 0``
);

val toLowercase_precond_def = new_definition (
  "toLowercase_precond_def",
  ``toLowercase_precond (s : num list) <=> T``
);

val toLowercase_def = new_definition (
  "toLowercase_def",
  ``toLowercase (s : num list) =
      MAP
        (\c : num. if isUpperCase c then shift32 c else c)
        s``
);

val toLowercase_postcond_def = new_definition (
  "toLowercase_postcond_def",
  ``toLowercase_postcond
      (s : num list) (result : num list) <=>
      LENGTH result = LENGTH s /\
      (!i : num.
         i < LENGTH s ==>
         (isUpperCase (EL i s) ==>
          EL i result = shift32 (EL i s)) /\
         (~isUpperCase (EL i s) ==>
          EL i result = EL i s))``
);

val toLowercase_spec_satisfied =
  ``!s : num list.
      toLowercase_isUnicodeString s ==>
      toLowercase_precond s ==>
      toLowercase_postcond s (toLowercase s)``;
