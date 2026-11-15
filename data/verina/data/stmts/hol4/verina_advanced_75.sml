(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_75,
  catalog title "task_code": the executable Kadane fold returns the greatest
  sum among all nonempty contiguous subarrays of a nonempty integer list.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val task_code_precond_def = new_definition (
  "task_code_precond_def",
  ``task_code_precond (sequence : int list) <=>
      0 < LENGTH sequence``
);

val task_code_step_def = new_definition (
  "task_code_step_def",
  ``task_code_step
      (acc : int # int) (x : int) =
      let cur = FST acc in
      let maxSoFar = SND acc in
      let newCur =
        if x <= cur + x then cur + x else x
      in
      let newMax =
        if newCur <= maxSoFar then maxSoFar else newCur
      in
        (newCur, newMax)``
);

val task_code_def = Define `
  (task_code ([] : int list) = 0) /\
  (task_code (x::xs) =
     SND (FOLDL task_code_step (x, x) xs))
`;

val task_code_subarrays_def = new_definition (
  "task_code_subarrays_def",
  ``task_code_subarrays (sequence : int list) =
      FLAT
        (MAP
          (\start.
             MAP
               (\len. TAKE len (DROP start sequence))
               (COUNT_LIST (LENGTH sequence - start + 1)))
          (COUNT_LIST (LENGTH sequence + 1)))``
);

val task_code_subarraySums_def = new_definition (
  "task_code_subarraySums_def",
  ``task_code_subarraySums (sequence : int list) =
      MAP
        (\subarray : int list.
           FOLDL (\acc : int. \x : int. acc + x) 0 subarray)
        (FILTER
          (\subarray : int list. subarray <> [])
          (task_code_subarrays sequence))``
);

val task_code_postcond_def = new_definition (
  "task_code_postcond_def",
  ``task_code_postcond
      (sequence : int list) (result : int) <=>
      MEM result (task_code_subarraySums sequence) /\
      EVERY
        (\sum : int. sum <= result)
        (task_code_subarraySums sequence)``
);

val task_code_spec_satisfied =
  ``!sequence : int list.
      task_code_precond sequence ==>
      task_code_postcond sequence (task_code sequence)``;
