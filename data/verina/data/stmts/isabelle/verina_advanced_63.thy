(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_63,
  catalog title "removeDuplicates": an executable recursive accumulator counts
  the distinct integers in a nondecreasing list, together with its precondition,
  duplicate-removal postcondition, and correctness contract. This file contains
  no proof.
*)

theory verina_advanced_63
  imports Main
begin

definition removeDuplicates_precond :: "int list \<Rightarrow> bool" where
  "removeDuplicates_precond nums \<longleftrightarrow> sorted nums"

fun removeDuplicates_countUniques ::
    "int \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> nat" where
  "removeDuplicates_countUniques prev [] k = k"
| "removeDuplicates_countUniques prev (head # tail) k =
    (if head = prev
     then removeDuplicates_countUniques prev tail k
     else removeDuplicates_countUniques head tail (k + 1))"

definition removeDuplicates :: "int list \<Rightarrow> nat" where
  "removeDuplicates nums =
    (case nums of
       [] \<Rightarrow> 0
     | h # t \<Rightarrow> removeDuplicates_countUniques h t 1)"

definition removeDuplicates_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> bool" where
  "removeDuplicates_postcond nums result \<longleftrightarrow>
    result - length (remdups nums) = 0 \<and>
    length (remdups nums) \<le> result"

theorem removeDuplicates_spec_satisfied:
  assumes "removeDuplicates_precond nums"
  shows "removeDuplicates_postcond nums (removeDuplicates nums)"
  sorry

end
