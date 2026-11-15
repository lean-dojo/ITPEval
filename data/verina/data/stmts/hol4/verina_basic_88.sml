(*
  Statement-only formalization of VERINA corpus artifact verina_basic_88,
  catalog title "ToArray": the executable conversion preserves the length and
  every indexed integer when converting a list to an array. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val ToArray_getBang_def = new_definition (
  "ToArray_getBang_def",
  ``ToArray_getBang (xs : int list) (index : num) =
      if index < LENGTH xs then EL index xs else (0 : int)``
);

val ToArray_precond_def = new_definition (
  "ToArray_precond_def",
  ``ToArray_precond (xs : int list) <=> T``
);

val ToArray_def = new_definition (
  "ToArray_def",
  ``ToArray (xs : int list) = xs``
);

val ToArray_postcond_def = new_definition (
  "ToArray_postcond_def",
  ``ToArray_postcond
      (xs : int list) (result : int list) <=>
      LENGTH result = LENGTH xs /\
      (!i : num.
         i < LENGTH xs ==>
         ToArray_getBang result i = ToArray_getBang xs i)``
);

val ToArray_spec_satisfied =
  ``!xs : int list.
      ToArray_precond xs ==>
      ToArray_postcond xs (ToArray xs)``;
