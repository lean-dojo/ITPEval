(*
  Statement-only formalization of VERINA corpus artifact verina_basic_75,
  catalog title "minArray": the executable left-to-right scan returns a
  least element of a nonempty integer array under its minimum-element
  correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val minArray_precond_def = new_definition (
  "minArray_precond_def",
  ``minArray_precond (a : int list) <=>
      0 < LENGTH a``
);

val minArray_nthD_def = Define `
  (minArray_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (minArray_nthD
      0 (x::xs) = x) /\
  (minArray_nthD
      (SUC index) (x::xs) =
     minArray_nthD index xs)
`;

val minArray_auxFuel_def = Define `
  (minArray_auxFuel
      (a : int list)
      (index : num)
      (current : int)
      0 =
     current) /\
  (minArray_auxFuel
      a index current (SUC fuel) =
     if index < LENGTH a then
       let new_current =
         if current > minArray_nthD index a then
           minArray_nthD index a
         else
           current
       in
         minArray_auxFuel
           a (index + 1) new_current fuel
     else
       current)
`;

val minArray_aux_def = new_definition (
  "minArray_aux_def",
  ``minArray_aux
      (a : int list) (index : num) (current : int) =
      minArray_auxFuel a index current (LENGTH a - index)``
);

val minArray_def = new_definition (
  "minArray_def",
  ``minArray (a : int list) =
      minArray_aux a 1 (minArray_nthD 0 a)``
);

val minArray_postcond_def = new_definition (
  "minArray_postcond_def",
  ``minArray_postcond
      (a : int list) (result : int) <=>
      (!k : num.
         k < LENGTH a ==>
         result <= minArray_nthD k a) /\
      (?k : num.
         k < LENGTH a /\
         result = minArray_nthD k a)``
);

val minArray_spec_satisfied =
  ``!a : int list.
      minArray_precond a ==>
      minArray_postcond a (minArray a)``;
