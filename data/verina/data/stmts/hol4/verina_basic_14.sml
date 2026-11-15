(*
  Statement-only formalization of VERINA corpus artifact verina_basic_14,
  catalog title "containsZ": the executable Boolean program tests whether a
  Unicode-scalar string contains lowercase 'z' or uppercase 'Z' and satisfies
  the exact membership correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val containsZ_isUnicodeScalar_def = new_definition (
  "containsZ_isUnicodeScalar_def",
  ``containsZ_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val containsZ_isUnicodeString_def = new_definition (
  "containsZ_isUnicodeString_def",
  ``containsZ_isUnicodeString (s : num list) <=>
      EVERY containsZ_isUnicodeScalar s``
);

val containsZ_precond_def = new_definition (
  "containsZ_precond_def",
  ``containsZ_precond (s : num list) <=> T``
);

val containsZ_def = new_definition (
  "containsZ_def",
  ``containsZ (s : num list) =
      EXISTS (\c : num. c = 122 \/ c = 90) s``
);

val containsZ_postcond_def = new_definition (
  "containsZ_postcond_def",
  ``containsZ_postcond (s : num list) (result : bool) <=>
      (EXISTS (\c : num. c = 122 \/ c = 90) s <=> result)``
);

val containsZ_spec_satisfied =
  ``!s : num list.
      containsZ_isUnicodeString s ==>
      containsZ_precond s ==>
      containsZ_postcond s (containsZ s)``;
