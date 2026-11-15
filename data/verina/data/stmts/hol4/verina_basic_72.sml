(*
  Statement-only formalization of VERINA corpus artifact verina_basic_72,
  catalog title "append": the executable integer-array program copies every
  input element and appends one integer, with its unrestricted precondition
  and indexed postcondition correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val append_getBang_def = new_definition (
  "append_getBang_def",
  ``append_getBang (xs : int list) (index : num) =
      if index < LENGTH xs then EL index xs else (0 : int)``
);

val append_precond_def = new_definition (
  "append_precond_def",
  ``append_precond (a : int list) (b : int) <=> T``
);

val append_copyFuel_def = Define `
  (append_copyFuel
      0
      (a : int list)
      (i : num)
      (acc : int list) =
     acc) /\
  (append_copyFuel
      (SUC fuel)
      a
      i
      acc =
     if i < LENGTH a then
       append_copyFuel
         fuel
         a
         (i + 1)
         (acc ++ [append_getBang a i])
     else
       acc)
`;

val copy_def = new_definition (
  "copy_def",
  ``copy
      (a : int list) (i : num) (acc : int list) =
      append_copyFuel (SUC (LENGTH a - i)) a i acc``
);

val append_def = new_definition (
  "append_def",
  ``append (a : int list) (b : int) =
      let c_initial = copy a 0 []
      in
        let c_full = c_initial ++ [b]
        in
          c_full``
);

val append_postcond_def = new_definition (
  "append_postcond_def",
  ``append_postcond
      (a : int list) (b : int) (result : int list) <=>
      (!i : num.
         i < LENGTH a ==>
         append_getBang result i = append_getBang a i) /\
      append_getBang result (LENGTH a) = b /\
      LENGTH result = LENGTH a + 1``
);

val append_spec_satisfied =
  ``!(a : int list) (b : int).
      append_precond a b ==>
      append_postcond a b (append a b)``;
