(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_46,
  catalog title "maxSubarraySum": an executable integer-list scan with an
  all-negative check computes a nonnegative contiguous-subarray maximum,
  together with its unconditional precondition and maximality postcondition
  over all contiguous slices, including the empty slice. This file contains
  no proof.
*)

theory verina_advanced_46
  imports Main
begin

definition maxSubarraySum_precond :: "int list \<Rightarrow> bool" where
  "maxSubarraySum_precond numbers \<longleftrightarrow> True"

fun maxSubarraySum_isAllNegative :: "int list \<Rightarrow> bool" where
  "maxSubarraySum_isAllNegative [] = True"
| "maxSubarraySum_isAllNegative (x # xs) =
    (if x \<ge> 0 then False else maxSubarraySum_isAllNegative xs)"

fun maxSubarraySum_findMaxProduct ::
    "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "maxSubarraySum_findMaxProduct [] currMax currSum = currMax"
| "maxSubarraySum_findMaxProduct [x] currMax currSum = max currMax x"
| "maxSubarraySum_findMaxProduct (x # y # rest) currMax currSum =
    (let newSum = max y (currSum + y);
         newMax = max currMax newSum
     in maxSubarraySum_findMaxProduct (y # rest) newMax newSum)"

definition maxSubarraySum_handleList :: "int list \<Rightarrow> nat" where
  "maxSubarraySum_handleList numbers =
    (case numbers of
       [] \<Rightarrow> 0
     | x # rest \<Rightarrow>
         if maxSubarraySum_isAllNegative (x # rest)
         then 0
         else
           nat
             (maxSubarraySum_findMaxProduct
               (x # rest) (max 0 x) (max 0 x)))"

definition maxSubarraySum :: "int list \<Rightarrow> int" where
  "maxSubarraySum numbers = int (maxSubarraySum_handleList numbers)"

definition maxSubarraySum_subArraySums :: "int list \<Rightarrow> int list" where
  "maxSubarraySum_subArraySums numbers =
    concat
      (map
        (\<lambda>start.
          map
            (\<lambda>len. sum_list (take len (drop start numbers)))
            [0..<(length numbers - start + 1)])
        [0..<(length numbers + 1)])"

definition maxSubarraySum_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "maxSubarraySum_postcond numbers result \<longleftrightarrow>
    (let subArraySums = maxSubarraySum_subArraySums numbers
     in
       list_ex (\<lambda>subArraySum. subArraySum = result) subArraySums \<and>
       list_all (\<lambda>subArraySum. subArraySum \<le> result) subArraySums)"

theorem maxSubarraySum_spec_satisfied:
  assumes "maxSubarraySum_precond numbers"
  shows "maxSubarraySum_postcond numbers (maxSubarraySum numbers)"
  sorry

end
