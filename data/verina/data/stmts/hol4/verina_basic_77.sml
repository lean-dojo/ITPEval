(*
  Statement-only formalization of VERINA corpus artifact verina_basic_77,
  catalog title "modify_array_element": the exact executable nested
  natural-number array update replaces one selected inner element and states
  its bounds precondition and preservation postcondition. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val modify_array_element_outerGetBang_def = new_definition (
  "modify_array_element_outerGetBang_def",
  ``modify_array_element_outerGetBang
      (arr : num list list) (index : num) =
      if index < LENGTH arr then
        EL index arr
      else
        ([] : num list)``
);

val modify_array_element_innerGetBang_def = new_definition (
  "modify_array_element_innerGetBang_def",
  ``modify_array_element_innerGetBang
      (arr : num list) (index : num) =
      if index < LENGTH arr then
        EL index arr
      else
        (0 : num)``
);

val modify_array_element_precond_def = new_definition (
  "modify_array_element_precond_def",
  ``modify_array_element_precond
      (arr : num list list) (index1 : num)
      (index2 : num) (value : num) <=>
      index1 < LENGTH arr /\
      index2 <
        LENGTH (modify_array_element_outerGetBang arr index1)``
);

val updateInner_def = new_definition (
  "updateInner_def",
  ``updateInner
      (arr : num list) (index : num) (value : num) =
      if index < LENGTH arr then
        LUPDATE value index arr
      else
        arr``
);

val modify_array_element_setOuterBang_def = new_definition (
  "modify_array_element_setOuterBang_def",
  ``modify_array_element_setOuterBang
      (arr : num list list) (index : num) (value : num list) =
      if index < LENGTH arr then
        LUPDATE value index arr
      else
        arr``
);

val modify_array_element_def = new_definition (
  "modify_array_element_def",
  ``modify_array_element
      (arr : num list list) (index1 : num)
      (index2 : num) (value : num) =
      let inner =
        modify_array_element_outerGetBang arr index1
      in
        let innerUpdated =
          updateInner inner index2 value
        in
          modify_array_element_setOuterBang
            arr index1 innerUpdated``
);

val modify_array_element_postcond_def = new_definition (
  "modify_array_element_postcond_def",
  ``modify_array_element_postcond
      (arr : num list list) (index1 : num)
      (index2 : num) (value : num)
      (result : num list list) <=>
      LENGTH result = LENGTH arr /\
      LENGTH (modify_array_element_outerGetBang result index1) =
        LENGTH (modify_array_element_outerGetBang arr index1) /\
      (!i : num.
         i < LENGTH arr /\ i <> index1 ==>
         modify_array_element_outerGetBang result i =
         modify_array_element_outerGetBang arr i) /\
      (!j : num.
         j <
           LENGTH (modify_array_element_outerGetBang arr index1) /\
         j <> index2 ==>
         modify_array_element_innerGetBang
           (modify_array_element_outerGetBang result index1) j =
         modify_array_element_innerGetBang
           (modify_array_element_outerGetBang arr index1) j) /\
      modify_array_element_innerGetBang
        (modify_array_element_outerGetBang result index1) index2 =
      value``
);

val modify_array_element_spec_satisfied =
  ``!(arr : num list list) (index1 : num)
      (index2 : num) (value : num).
      modify_array_element_precond arr index1 index2 value ==>
      modify_array_element_postcond
        arr index1 index2 value
        (modify_array_element arr index1 index2 value)``;
