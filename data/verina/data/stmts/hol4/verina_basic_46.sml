(*
  Statement-only formalization of VERINA corpus artifact verina_basic_46,
  catalog title "lastPosition": the executable full-array scan of a
  nondecreasing integer array returns the last index containing the specified
  element, or -1 when the element is absent. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val lastPosition_pairwise_def = Define `
  (lastPosition_pairwise ([] : int list) = T) /\
  (lastPosition_pairwise (x::xs) =
     (EVERY (\y : int. x <= y) xs /\
      lastPosition_pairwise xs))
`;

val lastPosition_precond_def = new_definition (
  "lastPosition_precond_def",
  ``lastPosition_precond
      (arr : int list) (elem : int) <=>
      lastPosition_pairwise arr``
);

val lastPosition_loopFuel_def = Define `
  (lastPosition_loopFuel
      0
      (arr : int list) (elem : int)
      (i : num) (pos : int) =
     pos) /\
  (lastPosition_loopFuel
      (SUC fuel) arr elem i pos =
     if i < LENGTH arr then
       if EL i arr = elem then
         lastPosition_loopFuel
           fuel arr elem (i + 1) (int_of_num i)
       else
         lastPosition_loopFuel
           fuel arr elem (i + 1) pos
     else
       pos)
`;

val lastPosition_loop_def = new_definition (
  "lastPosition_loop_def",
  ``lastPosition_loop
      (arr : int list) (elem : int)
      (i : num) (pos : int) =
      lastPosition_loopFuel
        (LENGTH arr - i) arr elem i pos``
);

val lastPosition_def = new_definition (
  "lastPosition_def",
  ``lastPosition (arr : int list) (elem : int) =
      lastPosition_loop arr elem 0 (~1 : int)``
);

val lastPosition_postcond_def = new_definition (
  "lastPosition_postcond_def",
  ``lastPosition_postcond
      (arr : int list) (elem : int) (result : int) <=>
      (result = (~1 : int) \/ 0 <= result) /\
      (0 <= result ==>
        Num result < LENGTH arr /\
        EL (Num result) arr = elem /\
        EVERY
          (\x : int. x <> elem)
          (DROP (Num result + 1) arr)) /\
      (result = (~1 : int) ==>
        EVERY (\x : int. x <> elem) arr)``
);

val lastPosition_spec_satisfied =
  ``!(arr : int list) (elem : int).
      lastPosition_precond arr elem ==>
      lastPosition_postcond
        arr elem (lastPosition arr elem)``;
