(*
  Statement-only formalization of VERINA corpus artifact verina_basic_39,
  catalog title "rotateRight": the executable integer-list program rotates
  entries to the right by a natural-number offset using Euclidean modular
  indexing, and states its length and pointwise optional-indexing contract.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val rotateRight_intEmod_def = new_definition (
  "rotateRight_intEmod_def",
  ``rotateRight_intEmod (x : int) (y : int) =
      if y = 0 then
        x
      else if y < 0 then
        x % ~y
      else
        x % y``
);

val rotateRight_intToNat_def = new_definition (
  "rotateRight_intToNat_def",
  ``rotateRight_intToNat (x : int) =
      if x < 0 then 0 else Num x``
);

val rotateRight_headD_def = new_definition (
  "rotateRight_headD_def",
  ``rotateRight_headD (xs : int list) (default : int) =
      case xs of
        [] => default
      | x::rest => x``
);

val rotateRight_getD_def = new_definition (
  "rotateRight_getD_def",
  ``rotateRight_getD
      (xs : int list) (index : num) (default : int) =
      if index < LENGTH xs then EL index xs else default``
);

val rotateRight_getOpt_def = new_definition (
  "rotateRight_getOpt_def",
  ``rotateRight_getOpt (xs : int list) (index : num) =
      if index < LENGTH xs then
        SOME (EL index xs)
      else
        (NONE : int option)``
);

val rotateRight_index_def = new_definition (
  "rotateRight_index_def",
  ``rotateRight_index (len : num) (n : num) (i : num) =
      rotateRight_intToNat
        (rotateRight_intEmod
          (int_of_num i - int_of_num n + int_of_num len)
          (int_of_num len))``
);

val rotateRight_precond_def = new_definition (
  "rotateRight_precond_def",
  ``rotateRight_precond (l : int list) (n : num) <=> T``
);

val rotateRight_def = new_definition (
  "rotateRight_def",
  ``rotateRight (l : int list) (n : num) =
      let len = LENGTH l in
        if len = 0 then
          l
        else
          GENLIST
            (\i : num.
               rotateRight_getD
                 l
                 (rotateRight_index len n i)
                 (rotateRight_headD l 0))
            len``
);

val rotateRight_postcond_def = new_definition (
  "rotateRight_postcond_def",
  ``rotateRight_postcond
      (l : int list) (n : num) (result : int list) <=>
      LENGTH result = LENGTH l /\
      (!i : num.
         i < LENGTH l ==>
         rotateRight_getOpt result i =
         rotateRight_getOpt
           l (rotateRight_index (LENGTH l) n i))``
);

val rotateRight_spec_satisfied =
  ``!(l : int list) (n : num).
      rotateRight_precond l n ==>
      rotateRight_postcond l n (rotateRight l n)``;
