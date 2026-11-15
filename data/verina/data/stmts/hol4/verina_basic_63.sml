(*
  Statement-only formalization of VERINA corpus artifact verina_basic_63,
  catalog title "has_close_elements": the executable IEEE-754 binary64
  program detects whether a list contains two distinct positions whose
  absolute difference is below a nonnegative threshold, under its complete
  correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;
open binary_ieeeTheory machine_ieeeTheory;

val absDiff_def = new_definition (
  "absDiff_def",
  ``absDiff (a : word64) (b : word64) =
      let ab = fp64_sub roundTiesToEven a b in
      if fp64_lessThan ab fp64_posZero then
        fp64_sub roundTiesToEven b a
      else
        ab``
);

val has_close_elements_precond_def = new_definition (
  "has_close_elements_precond_def",
  ``has_close_elements_precond
      (numbers : word64 list) (thresh : word64) <=>
      fp64_lessEqual fp64_posZero thresh /\
      ~fp64_isNan thresh /\
      EVERY
        (\x : word64.
          ~fp64_isNan x /\ ~fp64_isInfinite x)
        numbers``
);

val has_close_elements_getD_def = new_definition (
  "has_close_elements_getD_def",
  ``has_close_elements_getD
      (numbers : word64 list) (index : num) =
      if index < LENGTH numbers then
        EL index numbers
      else
        fp64_posZero``
);

val has_close_elements_innerFuel_def = Define `
  (has_close_elements_innerFuel
      0
      (numbers : word64 list) (thresh : word64)
      (index : num) (index2 : num) =
     F) /\
  (has_close_elements_innerFuel
      (SUC fuel) numbers thresh index index2 =
     if index2 < index then
       let a = has_close_elements_getD numbers index2 in
       let b = has_close_elements_getD numbers index in
       let d = absDiff a b in
         if fp64_lessThan d thresh then
           T
         else
           has_close_elements_innerFuel
             fuel numbers thresh index (SUC index2)
     else
       F)
`;

val has_close_elements_outerFuel_def = Define `
  (has_close_elements_outerFuel
      0
      (numbers : word64 list) (thresh : word64)
      (index : num) =
     F) /\
  (has_close_elements_outerFuel
      (SUC fuel) numbers thresh index =
     if index < LENGTH numbers then
       if has_close_elements_innerFuel
            (SUC index) numbers thresh index 0
       then
         T
       else
         has_close_elements_outerFuel
           fuel numbers thresh (SUC index)
     else
       F)
`;

val has_close_elements_def = new_definition (
  "has_close_elements_def",
  ``has_close_elements
      (numbers : word64 list) (thresh : word64) =
      has_close_elements_outerFuel
        (SUC (LENGTH numbers)) numbers thresh 0``
);

val has_close_elements_pairwise_def = Define `
  (has_close_elements_pairwise
      (thresh : word64) ([] : word64 list) =
     T) /\
  (has_close_elements_pairwise
      thresh (a::rest) =
     (EVERY
        (\b : word64.
          fp64_lessEqual thresh (absDiff a b))
        rest /\
      has_close_elements_pairwise thresh rest))
`;

val has_close_elements_postcond_def = new_definition (
  "has_close_elements_postcond_def",
  ``has_close_elements_postcond
      (numbers : word64 list) (thresh : word64)
      (result : bool) <=>
      (~result <=>
       has_close_elements_pairwise thresh numbers)``
);

val has_close_elements_spec_satisfied =
  ``!(numbers : word64 list) (thresh : word64).
      has_close_elements_precond numbers thresh ==>
      has_close_elements_postcond
        numbers thresh
        (has_close_elements numbers thresh)``;
