(*
  Statement-only formalization of VERINA corpus artifact verina_basic_97,
  catalog title "TestArrayElements": the executable integer-array program sets
  the element at a valid natural-number index to 60, preserves the array length
  and every other element, and satisfies that update contract. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val TestArrayElements_getBang_def = new_definition (
  "TestArrayElements_getBang_def",
  ``TestArrayElements_getBang (a : int list) (i : num) =
      if i < LENGTH a then EL i a else (0 : int)``
);

val TestArrayElements_setBang_def = new_definition (
  "TestArrayElements_setBang_def",
  ``TestArrayElements_setBang
      (a : int list) (i : num) (value : int) =
      if i < LENGTH a then LUPDATE value i a else a``
);

val TestArrayElements_precond_def = new_definition (
  "TestArrayElements_precond_def",
  ``TestArrayElements_precond (a : int list) (j : num) <=>
      j < LENGTH a``
);

val TestArrayElements_def = new_definition (
  "TestArrayElements_def",
  ``TestArrayElements (a : int list) (j : num) =
      TestArrayElements_setBang a j 60``
);

val TestArrayElements_postcond_def = new_definition (
  "TestArrayElements_postcond_def",
  ``TestArrayElements_postcond
      (a : int list) (j : num) (result : int list) <=>
      LENGTH result = LENGTH a /\
      TestArrayElements_getBang result j = 60 /\
      (!k : num.
         k < LENGTH a ==>
         k <> j ==>
         TestArrayElements_getBang result k =
         TestArrayElements_getBang a k)``
);

val TestArrayElements_spec_satisfied =
  ``!(a : int list) (j : num).
      TestArrayElements_precond a j ==>
      TestArrayElements_postcond
        a j (TestArrayElements a j)``;
