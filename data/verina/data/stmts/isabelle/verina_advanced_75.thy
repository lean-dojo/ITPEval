(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_75,
  catalog title "task_code": Kadane's executable integer-list scan computes
  the maximum sum of a nonempty contiguous subarray, together with its
  nonempty-input precondition and maximality postcondition. This file contains
  no proof.
*)

theory verina_advanced_75
  imports Main
begin

definition task_code_precond :: "int list \<Rightarrow> bool" where
  "task_code_precond sequence \<longleftrightarrow> length sequence > 0"

definition task_code_step :: "int \<times> int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "task_code_step acc x =
    (let cur = fst acc;
         maxSoFar = snd acc;
         newCur = (if cur + x \<ge> x then cur + x else x);
         newMax = (if maxSoFar \<ge> newCur then maxSoFar else newCur)
     in (newCur, newMax))"

fun task_code :: "int list \<Rightarrow> int" where
  "task_code [] = 0"
| "task_code (x # xs) = snd (foldl task_code_step (x, x) xs)"

definition task_code_subArrays :: "int list \<Rightarrow> int list list" where
  "task_code_subArrays sequence =
    concat
      (map
        (\<lambda>start.
          map
            (\<lambda>len. take len (drop start sequence))
            [0..<(length sequence - start + 1)])
        [0..<(length sequence + 1)])"

definition task_code_subArraySums :: "int list \<Rightarrow> int list" where
  "task_code_subArraySums sequence =
    map sum_list (filter (\<lambda>subArray. subArray \<noteq> [])
      (task_code_subArrays sequence))"

definition task_code_postcond :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "task_code_postcond sequence result \<longleftrightarrow>
    (let subArraySums = task_code_subArraySums sequence
     in result \<in> set subArraySums \<and>
        list_all (\<lambda>subArraySum. subArraySum \<le> result) subArraySums)"

theorem task_code_spec_satisfied:
  assumes "task_code_precond sequence"
  shows "task_code_postcond sequence (task_code sequence)"
  sorry

end
