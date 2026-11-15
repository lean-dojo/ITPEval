(*
  Statement-only formalization of VERINA corpus artifact verina_basic_82,
  catalog title "remove_front": the executable integer-array program copies
  all elements after the first into a new array and satisfies the nonempty
  input, length, and indexed-element correctness contract. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val remove_front_getBang_def = new_definition (
  "remove_front_getBang_def",
  ``remove_front_getBang (xs : int list) (index : num) =
      if index < LENGTH xs then EL index xs else (0 : int)``
);

val remove_front_precond_def = new_definition (
  "remove_front_precond_def",
  ``remove_front_precond (a : int list) <=>
      LENGTH a > 0``
);

val copyFromFuel_def = Define `
  (copyFromFuel
      0
      (a : int list)
      (i : num)
      (acc : int list) =
     acc) /\
  (copyFromFuel
      (SUC fuel)
      a
      i
      acc =
     if i < LENGTH a then
       copyFromFuel
         fuel
         a
         (i + 1)
         (acc ++ [remove_front_getBang a i])
     else
       acc)
`;

val copyFrom_def = new_definition (
  "copyFrom_def",
  ``copyFrom
      (a : int list) (i : num) (acc : int list) =
      copyFromFuel (SUC (LENGTH a - i)) a i acc``
);

val remove_front_def = new_definition (
  "remove_front_def",
  ``remove_front (a : int list) =
      if LENGTH a > 0 then
        copyFrom a 1 []
      else
        ([] : int list)``
);

val remove_front_postcond_def = new_definition (
  "remove_front_postcond_def",
  ``remove_front_postcond
      (a : int list) (result : int list) <=>
      LENGTH a > 0 /\
      LENGTH result = LENGTH a - 1 /\
      (!i : num.
         i < LENGTH result ==>
         remove_front_getBang result i =
         remove_front_getBang a (i + 1))``
);

val remove_front_spec_satisfied =
  ``!a : int list.
      remove_front_precond a ==>
      remove_front_postcond a (remove_front a)``;
