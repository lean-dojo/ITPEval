(*
  Statement-only formalization of VERINA corpus artifact verina_basic_74,
  catalog title "maxArray": the executable left-to-right scan returns a
  greatest element of a nonempty integer array under its maximum-element
  correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val maxArray_precond_def = new_definition (
  "maxArray_precond_def",
  ``maxArray_precond (a : int list) <=>
      0 < LENGTH a``
);

val maxArray_nthD_def = Define `
  (maxArray_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (maxArray_nthD
      0 (x::xs) = x) /\
  (maxArray_nthD
      (SUC index) (x::xs) =
     maxArray_nthD index xs)
`;

val maxArray_auxFuel_def = Define `
  (maxArray_auxFuel
      (a : int list)
      (index : num)
      (current : int)
      0 =
     current) /\
  (maxArray_auxFuel
      a index current (SUC fuel) =
     if index < LENGTH a then
       let new_current =
         if current > maxArray_nthD index a then
           current
         else
           maxArray_nthD index a
       in
         maxArray_auxFuel
           a (index + 1) new_current fuel
     else
       current)
`;

val maxArray_aux_def = new_definition (
  "maxArray_aux_def",
  ``maxArray_aux
      (a : int list) (index : num) (current : int) =
      maxArray_auxFuel a index current (LENGTH a - index)``
);

val maxArray_def = new_definition (
  "maxArray_def",
  ``maxArray (a : int list) =
      maxArray_aux a 1 (maxArray_nthD 0 a)``
);

val maxArray_postcond_def = new_definition (
  "maxArray_postcond_def",
  ``maxArray_postcond
      (a : int list) (result : int) <=>
      (!k : num.
         k < LENGTH a ==>
         maxArray_nthD k a <= result) /\
      (?k : num.
         k < LENGTH a /\
         result = maxArray_nthD k a)``
);

val maxArray_spec_satisfied =
  ``!a : int list.
      maxArray_precond a ==>
      maxArray_postcond a (maxArray a)``;
