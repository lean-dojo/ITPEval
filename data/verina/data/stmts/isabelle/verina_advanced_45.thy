(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_45,
  catalog title "maxSubarraySum": an executable integer-list scan computes the
  maximum sum of a nonempty contiguous subarray, returning zero for the empty
  list, together with its precondition and maximality contract. This file
  contains no proof.
*)

theory verina_advanced_45
  imports Main
begin

definition maxSubarraySum_precond :: "int list \<Rightarrow> bool" where
  "maxSubarraySum_precond xs \<longleftrightarrow> True"

fun maxSubarraySum_helper ::
    "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "maxSubarraySum_helper [] curMax globalMax = globalMax"
| "maxSubarraySum_helper (x # rest) curMax globalMax =
    (let newCurMax = max x (curMax + x);
         newGlobal = max globalMax newCurMax
     in maxSubarraySum_helper rest newCurMax newGlobal)"

definition maxSubarraySum :: "int list \<Rightarrow> int" where
  "maxSubarraySum xs =
    (case xs of
       [] \<Rightarrow> 0
     | x # rest \<Rightarrow> maxSubarraySum_helper rest x x)"

definition maxSubarraySum_subarraySums :: "int list \<Rightarrow> int list" where
  "maxSubarraySum_subarraySums xs =
    concat
      (map
        (\<lambda>start.
          map
            (\<lambda>len. sum_list (take len (drop start xs)))
            [1..<(length xs - start + 1)])
        [0..<(length xs + 1)])"

definition maxSubarraySum_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "maxSubarraySum_postcond xs result \<longleftrightarrow>
    (let subarraySums = maxSubarraySum_subarraySums xs
     in case xs of
          [] \<Rightarrow> result = 0
        | _ \<Rightarrow>
            list_ex (\<lambda>subarraySum. subarraySum = result) subarraySums \<and>
            list_all (\<lambda>subarraySum. subarraySum \<le> result)
              subarraySums)"

theorem maxSubarraySum_spec_satisfied:
  assumes "maxSubarraySum_precond xs"
  shows "maxSubarraySum_postcond xs (maxSubarraySum xs)"
  sorry

end
