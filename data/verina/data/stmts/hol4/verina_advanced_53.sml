(*
  Statement-only formalization of VERINA artifact verina_advanced_53,
  cataloged as "minimumRightShifts": the executable bounded search returns
  the least right rotation that makes a duplicate-free integer list
  nondecreasing, or -1 when no such rotation exists. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val minimumRightShifts_precond_def = new_definition (
  "minimumRightShifts_precond_def",
  ``minimumRightShifts_precond (nums : int list) <=>
      ALL_DISTINCT nums``
);

val minimumRightShifts_isSortedAux_def = Define `
  (minimumRightShifts_isSortedAux ([] : int list) = T) /\
  (minimumRightShifts_isSortedAux [x] = T) /\
  (minimumRightShifts_isSortedAux (x::y::xs) =
     if x <= y then
       minimumRightShifts_isSortedAux (y::xs)
     else
       F)
`;

val minimumRightShifts_rightShiftOnce_def = new_definition (
  "minimumRightShifts_rightShiftOnce_def",
  ``minimumRightShifts_rightShiftOnce (nums : int list) =
      case REVERSE nums of
        [] => []
      | last::revInit => last::REVERSE revInit``
);

val minimumRightShifts_checkShiftsFuel_def = Define `
  (minimumRightShifts_checkShiftsFuel
      0
      (n : num)
      (shifts_count : num)
      (current_list : int list) =
     (-1 : int)) /\
  (minimumRightShifts_checkShiftsFuel
      (SUC fuel) n shifts_count current_list =
     if shifts_count >= n then
       (-1 : int)
     else if minimumRightShifts_isSortedAux current_list then
       int_of_num shifts_count
     else
       minimumRightShifts_checkShiftsFuel
         fuel
         n
         (shifts_count + 1)
         (minimumRightShifts_rightShiftOnce current_list))
`;

val minimumRightShifts_checkShifts_def = new_definition (
  "minimumRightShifts_checkShifts_def",
  ``minimumRightShifts_checkShifts
      (n : num)
      (shifts_count : num)
      (current_list : int list) =
      minimumRightShifts_checkShiftsFuel
        (n - shifts_count) n shifts_count current_list``
);

val minimumRightShifts_def = new_definition (
  "minimumRightShifts_def",
  ``minimumRightShifts (nums : int list) =
      let n = LENGTH nums in
        if n <= 1 then
          (0 : int)
        else if minimumRightShifts_isSortedAux nums then
          (0 : int)
        else
          minimumRightShifts_checkShifts
            n 1 (minimumRightShifts_rightShiftOnce nums)``
);

val minimumRightShifts_pairwise_def = Define `
  (minimumRightShifts_pairwise ([] : int list) = T) /\
  (minimumRightShifts_pairwise (x::xs) =
     (EVERY (\y : int. x <= y) xs /\
      minimumRightShifts_pairwise xs))
`;

val minimumRightShifts_rotateRight_def = Define `
  (minimumRightShifts_rotateRight
      0 (nums : int list) =
     nums) /\
  (minimumRightShifts_rotateRight
      (SUC k) nums =
     minimumRightShifts_rotateRight
       k (minimumRightShifts_rightShiftOnce nums))
`;

val minimumRightShifts_postcond_def = new_definition (
  "minimumRightShifts_postcond_def",
  ``minimumRightShifts_postcond
      (nums : int list) (result : int) <=>
      let n = LENGTH nums in
        if n <= 1 then
          result = 0
        else
          (0 <= result /\
           result < int_of_num n /\
           minimumRightShifts_pairwise
             (minimumRightShifts_rotateRight (Num result) nums) /\
           EVERY
             (\j : num.
                ~minimumRightShifts_pairwise
                  (minimumRightShifts_rotateRight j nums))
             (COUNT_LIST (Num result))) \/
          (result = -1 /\
           EVERY
             (\k : num.
                ~minimumRightShifts_pairwise
                  (minimumRightShifts_rotateRight k nums))
             (COUNT_LIST n))``
);

val minimumRightShifts_spec_satisfied =
  ``!nums : int list.
      minimumRightShifts_precond nums ==>
      minimumRightShifts_postcond
        nums (minimumRightShifts nums)``;
