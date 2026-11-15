(*
  Statement-only formalization of VERINA artifact verina_advanced_28,
  cataloged as "longestConsecutive": the executable bounded search returns
  the maximum length of a consecutive-integer streak in a duplicate-free
  integer list. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val longestConsecutive_precond_def = new_definition (
  "longestConsecutive_precond_def",
  ``longestConsecutive_precond (nums : int list) <=>
      ALL_DISTINCT nums``
);

val longestConsecutive_natMax_def = new_definition (
  "longestConsecutive_natMax_def",
  ``longestConsecutive_natMax (m : num) (n : num) =
      if m < n then n else m``
);

val longestConsecutive_extend_def = Define `
  (longestConsecutive_extend
      0
      (members : int list)
      (current : int)
      (length : num) =
     length) /\
  (longestConsecutive_extend
      (SUC fuel)
      members
      current
      length =
     if MEM (current + 1) members then
       longestConsecutive_extend
         fuel members (current + 1) (length + 1)
     else
       length)
`;

val longestConsecutive_scan_def = Define `
  (longestConsecutive_scan
      (members : int list)
      ([] : int list)
      (best : num) =
     best) /\
  (longestConsecutive_scan
      members
      (x::xs)
      best =
     if ~(MEM (x - 1) members) then
       let length =
         longestConsecutive_extend
           (LENGTH members) members x 1
       in
         longestConsecutive_scan
           members xs (longestConsecutive_natMax best length)
     else
       longestConsecutive_scan members xs best)
`;

val longestConsecutive_def = new_definition (
  "longestConsecutive_def",
  ``longestConsecutive (nums : int list) =
      longestConsecutive_scan nums nums 0``
);

val longestConsecutive_insert_def = Define `
  (longestConsecutive_insert
      (x : int) ([] : int list) =
     [x]) /\
  (longestConsecutive_insert x (y::ys) =
     if x <= y then
       x::y::ys
     else
       y::longestConsecutive_insert x ys)
`;

val longestConsecutive_sort_def = Define `
  (longestConsecutive_sort ([] : int list) =
     ([] : int list)) /\
  (longestConsecutive_sort (x::xs) =
     longestConsecutive_insert x (longestConsecutive_sort xs))
`;

val longestConsecutive_isConsecutiveFrom_def = Define `
  (longestConsecutive_isConsecutiveFrom
      (base : int)
      (index : num)
      ([] : int list) =
     T) /\
  (longestConsecutive_isConsecutiveFrom
      base
      index
      (x::xs) =
     (x = int_of_num index + base /\
      longestConsecutive_isConsecutiveFrom base (SUC index) xs))
`;

val isConsecutive_def = new_definition (
  "isConsecutive_def",
  ``isConsecutive (seq : int list) =
      case seq of
        [] => T
      | x::xs =>
          longestConsecutive_isConsecutiveFrom x 0 (x::xs)``
);

val longestConsecutive_consecutiveSublistLens_def = new_definition (
  "longestConsecutive_consecutiveSublistLens_def",
  ``longestConsecutive_consecutiveSublistLens (nums : int list) =
      let sorted_nums = longestConsecutive_sort nums in
      let sublists =
        FLAT
          (MAP
            (\start.
              MAP
                (\len. TAKE len (DROP start sorted_nums))
                (COUNT_LIST (LENGTH nums - start + 1)))
            (COUNT_LIST (LENGTH nums)))
      in
        MAP LENGTH (FILTER isConsecutive sublists)``
);

val longestConsecutive_postcond_def = new_definition (
  "longestConsecutive_postcond_def",
  ``longestConsecutive_postcond
      (nums : int list) (result : num) <=>
      let consec_sublist_lens =
        longestConsecutive_consecutiveSublistLens nums
      in
        (nums = [] ==> result = 0) /\
        (nums <> [] ==>
          MEM result consec_sublist_lens /\
          EVERY (\len : num. len <= result) consec_sublist_lens)``
);

val longestConsecutive_spec_satisfied =
  ``!nums : int list.
      longestConsecutive_precond nums ==>
      longestConsecutive_postcond
        nums (longestConsecutive nums)``;
