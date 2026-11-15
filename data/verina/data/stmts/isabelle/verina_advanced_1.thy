(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_1,
  catalog title "FindSingleNumber": an executable list program scans integers
  and returns the unique value occurring once when every input value occurs
  once or twice and exactly one list entry has occurrence count one. This file
  contains no proof.
*)

theory verina_advanced_1
  imports Main
begin

fun filterlist :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "filterlist x [] = []"
| "filterlist x (y # ys) =
    (if y = x then y # filterlist x ys else filterlist x ys)"

definition FindSingleNumber_precond :: "int list \<Rightarrow> bool" where
  "FindSingleNumber_precond nums \<longleftrightarrow>
    (let numsCount = map (\<lambda>x. count_list nums x) nums
     in list_all (\<lambda>count. count = 1 \<or> count = 2) numsCount \<and>
        count_list numsCount 1 = 1)"

fun findUnique :: "int list \<Rightarrow> int list \<Rightarrow> int" where
  "findUnique nums [] = 0"
| "findUnique nums (x # xs) =
    (let filtered = filterlist x nums;
         count = length filtered
     in if count = 1 then x else findUnique nums xs)"

definition FindSingleNumber :: "int list \<Rightarrow> int" where
  "FindSingleNumber nums = findUnique nums nums"

definition FindSingleNumber_postcond :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "FindSingleNumber_postcond nums result \<longleftrightarrow>
    length nums > 0 \<and>
    length (filterlist result nums) = 1 \<and>
    (\<forall>x. x \<in> set nums \<longrightarrow>
      (x = result \<or> length (filterlist x nums) = 2))"

theorem FindSingleNumber_spec_satisfied:
  assumes "FindSingleNumber_precond nums"
  shows "FindSingleNumber_postcond nums (FindSingleNumber nums)"
  sorry

end
