(*
  Statement-only formalization of VERINA corpus artifact verina_basic_94,
  catalog title "iter_copy": the executable integer-array program scans the
  input from index zero and appends each retrieved element to a fresh array,
  satisfying its unrestricted length and pointwise copy contract. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val iter_copy_getOpt_def = new_definition (
  "iter_copy_getOpt_def",
  ``iter_copy_getOpt (s : int list) (i : num) =
      if i < LENGTH s then SOME (EL i s) else NONE``
);

val iter_copy_getBang_def = new_definition (
  "iter_copy_getBang_def",
  ``iter_copy_getBang (s : int list) (i : num) =
      if i < LENGTH s then EL i s else (0 : int)``
);

val iter_copy_precond_def = new_definition (
  "iter_copy_precond_def",
  ``iter_copy_precond (s : int list) <=> T``
);

val iter_copy_loopFuel_def = Define `
  (iter_copy_loopFuel
      0
      (s : int list)
      (i : num)
      (acc : int list) =
     acc) /\
  (iter_copy_loopFuel
      (SUC fuel)
      s
      i
      acc =
     if i < LENGTH s then
       case iter_copy_getOpt s i of
         SOME value =>
           iter_copy_loopFuel
             fuel s (i + 1) (acc ++ [value])
       | NONE =>
           acc
     else
       acc)
`;

val iter_copy_loop_def = new_definition (
  "iter_copy_loop_def",
  ``iter_copy_loop
      (s : int list) (i : num) (acc : int list) =
      iter_copy_loopFuel (SUC (LENGTH s - i)) s i acc``
);

val iter_copy_def = new_definition (
  "iter_copy_def",
  ``iter_copy (s : int list) =
      iter_copy_loop s 0 []``
);

val iter_copy_postcond_def = new_definition (
  "iter_copy_postcond_def",
  ``iter_copy_postcond
      (s : int list) (result : int list) <=>
      LENGTH s = LENGTH result /\
      (!i : num.
         i < LENGTH s ==>
         iter_copy_getBang s i = iter_copy_getBang result i)``
);

val iter_copy_spec_satisfied =
  ``!s : int list.
      iter_copy_precond s ==>
      iter_copy_postcond s (iter_copy s)``;
