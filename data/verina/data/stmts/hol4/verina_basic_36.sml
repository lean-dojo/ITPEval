(*
  Statement-only formalization of VERINA corpus artifact verina_basic_36,
  catalog title "replaceWithColon": the executable Unicode-string map replaces
  every space, comma, or dot with a colon, preserves the string length, and
  leaves every other character unchanged. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val replaceWithColon_isUnicodeScalar_def = new_definition (
  "replaceWithColon_isUnicodeScalar_def",
  ``replaceWithColon_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val replaceWithColon_isUnicodeString_def = new_definition (
  "replaceWithColon_isUnicodeString_def",
  ``replaceWithColon_isUnicodeString (s : num list) <=>
      EVERY replaceWithColon_isUnicodeScalar s``
);

val isSpaceCommaDot_def = new_definition (
  "isSpaceCommaDot_def",
  ``isSpaceCommaDot (c : num) <=>
      c = 32 \/ c = 44 \/ c = 46``
);

val replaceWithColon_precond_def = new_definition (
  "replaceWithColon_precond_def",
  ``replaceWithColon_precond (s : num list) <=> T``
);

val replaceWithColon_def = new_definition (
  "replaceWithColon_def",
  ``replaceWithColon (s : num list) =
      MAP
        (\c : num. if isSpaceCommaDot c then 58 else c)
        s``
);

val replaceWithColon_postcond_def = new_definition (
  "replaceWithColon_postcond_def",
  ``replaceWithColon_postcond
      (s : num list) (result : num list) <=>
      LENGTH result = LENGTH s /\
      (!i : num.
         i < LENGTH s ==>
         (isSpaceCommaDot (EL i s) ==> EL i result = 58) /\
         (~isSpaceCommaDot (EL i s) ==>
          EL i result = EL i s))``
);

val replaceWithColon_spec_satisfied =
  ``!s : num list.
      replaceWithColon_isUnicodeString s ==>
      replaceWithColon_precond s ==>
      replaceWithColon_postcond s (replaceWithColon s)``;
