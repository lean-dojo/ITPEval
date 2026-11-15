(*
  Statement-only formalization of VERINA artifact verina_advanced_30,
  cataloged as "longestIncreasingStreak": the executable recursive scan
  returns the length of the longest strictly increasing contiguous streak
  in an integer list. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val longestIncreasingStreak_precond_def = new_definition (
  "longestIncreasingStreak_precond_def",
  ``longestIncreasingStreak_precond (nums : int list) <=> T``
);

val longestIncreasingStreak_natMax_def = new_definition (
  "longestIncreasingStreak_natMax_def",
  ``longestIncreasingStreak_natMax (m : num) (n : num) =
      if m < n then n else m``
);

val longestIncreasingStreak_aux_def = Define `
  (longestIncreasingStreak_aux
      ([] : int list)
      (prev : int option)
      (currLen : num)
      (maxLen : num) =
     longestIncreasingStreak_natMax currLen maxLen) /\
  (longestIncreasingStreak_aux
      (x::xs)
      prev
      currLen
      maxLen =
     case prev of
       NONE =>
         longestIncreasingStreak_aux
           xs (SOME x) 1
           (longestIncreasingStreak_natMax 1 maxLen)
     | SOME p =>
         if p < x then
           longestIncreasingStreak_aux
             xs (SOME x) (currLen + 1)
             (longestIncreasingStreak_natMax
                (currLen + 1) maxLen)
         else
           longestIncreasingStreak_aux
             xs (SOME x) 1
             (longestIncreasingStreak_natMax currLen maxLen))
`;

val longestIncreasingStreak_def = new_definition (
  "longestIncreasingStreak_def",
  ``longestIncreasingStreak (nums : int list) =
      longestIncreasingStreak_aux nums NONE 0 0``
);

val longestIncreasingStreak_safeGet_def = Define `
  (longestIncreasingStreak_safeGet
      ([] : int list) (index : num) = (0 : int)) /\
  (longestIncreasingStreak_safeGet
      (x::xs) 0 = x) /\
  (longestIncreasingStreak_safeGet
      (x::xs) (SUC index) =
     longestIncreasingStreak_safeGet xs index)
`;

val longestIncreasingStreak_postcond_def = new_definition (
  "longestIncreasingStreak_postcond_def",
  ``longestIncreasingStreak_postcond
      (nums : int list) (result : num) <=>
      (nums = [] ==> result = 0) /\
      (0 < result ==>
        EXISTS
          (\start.
             start + result <= LENGTH nums /\
             EVERY
               (\i.
                  longestIncreasingStreak_safeGet
                    nums (start + i) <
                  longestIncreasingStreak_safeGet
                    nums (start + i + 1))
               (COUNT_LIST (result - 1)) /\
             (start = 0 \/
              longestIncreasingStreak_safeGet
                nums (start - 1) >=
              longestIncreasingStreak_safeGet
                nums start) /\
             (start + result = LENGTH nums \/
              longestIncreasingStreak_safeGet
                nums (start + result - 1) >=
              longestIncreasingStreak_safeGet
                nums (start + result)))
          (COUNT_LIST (LENGTH nums - result + 1))) /\
      EVERY
        (\start.
           EXISTS
             (\i.
                start + i + 1 >= LENGTH nums \/
                longestIncreasingStreak_safeGet
                  nums (start + i) >=
                longestIncreasingStreak_safeGet
                  nums (start + i + 1))
             (COUNT_LIST result))
        (COUNT_LIST (LENGTH nums - result))``
);

val longestIncreasingStreak_spec_satisfied =
  ``!nums : int list.
      longestIncreasingStreak_precond nums ==>
      longestIncreasingStreak_postcond
        nums (longestIncreasingStreak nums)``;
