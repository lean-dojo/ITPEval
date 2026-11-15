(*
  Statement-only formalization of VERINA artifact verina_advanced_35,
  cataloged as "majorityElement": the executable counting search returns the
  integer occurring strictly more than half the input-list length, with zero
  as the fallback when no such integer exists. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val majorityElement_count_def = new_definition (
  "majorityElement_count_def",
  ``majorityElement_count (x : int) (nums : int list) =
      LENGTH (FILTER (\y : int. y = x) nums)``
);

val majorityElement_precond_def = new_definition (
  "majorityElement_precond_def",
  ``majorityElement_precond (nums : int list) <=>
      LENGTH nums > 0 /\
      EXISTS
        (\x : int.
          majorityElement_count x nums > LENGTH nums DIV 2)
        nums``
);

val majorityElement_find_def = Define `
  (majorityElement_find
      (nums : int list) ([] : int list) =
     (NONE : int option)) /\
  (majorityElement_find nums (x::xs) =
     if majorityElement_count x nums > LENGTH nums DIV 2 then
       SOME x
     else
       majorityElement_find nums xs)
`;

val majorityElement_def = new_definition (
  "majorityElement_def",
  ``majorityElement (nums : int list) =
      case majorityElement_find nums nums of
        NONE => (0 : int)
      | SOME x => x``
);

val majorityElement_postcond_def = new_definition (
  "majorityElement_postcond_def",
  ``majorityElement_postcond
      (nums : int list) (result : int) <=>
      let n = LENGTH nums
      in
        majorityElement_count result nums > n DIV 2 /\
        (!x : int.
          MEM x nums /\ x <> result ==>
          majorityElement_count x nums <= n DIV 2)``
);

val majorityElement_spec_satisfied =
  ``!nums : int list.
      majorityElement_precond nums ==>
      majorityElement_postcond nums (majorityElement nums)``;
