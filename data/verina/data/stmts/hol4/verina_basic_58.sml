(*
  Statement-only formalization of VERINA corpus artifact verina_basic_58,
  catalog title "double_array_elements": the executable indexed array update
  doubles every integer element using the original array and states its total
  precondition and element-wise correctness contract. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val double_array_elements_precond_def = new_definition (
  "double_array_elements_precond_def",
  ``double_array_elements_precond (s : int list) <=> T``
);

val double_array_elements_getBang_def = new_definition (
  "double_array_elements_getBang_def",
  ``double_array_elements_getBang
      (s : int list) (i : num) =
      if i < LENGTH s then EL i s else (0 : int)``
);

val double_array_elements_loopFuel_def = Define `
  (double_array_elements_loopFuel
      0
      (s_old : int list) (s : int list) (i : num) =
     s) /\
  (double_array_elements_loopFuel
      (SUC fuel) s_old s i =
     if i < LENGTH s then
       let new_s =
         LUPDATE
           ((2 : int) * double_array_elements_getBang s_old i)
           i
           s
       in
         double_array_elements_loopFuel
           fuel s_old new_s (i + 1)
     else
       s)
`;

val double_array_elements_aux_def = new_definition (
  "double_array_elements_aux_def",
  ``double_array_elements_aux
      (s_old : int list) (s : int list) (i : num) =
      double_array_elements_loopFuel
        (SUC (LENGTH s - i)) s_old s i``
);

val double_array_elements_def = new_definition (
  "double_array_elements_def",
  ``double_array_elements (s : int list) =
      double_array_elements_aux s s 0``
);

val double_array_elements_postcond_def = new_definition (
  "double_array_elements_postcond_def",
  ``double_array_elements_postcond
      (s : int list) (result : int list) <=>
      LENGTH result = LENGTH s /\
      (!i : num.
         i < LENGTH s ==>
         EL i result = (2 : int) * EL i s)``
);

val double_array_elements_spec_satisfied =
  ``!s : int list.
      double_array_elements_precond s ==>
      double_array_elements_postcond
        s
        (double_array_elements s)``;
