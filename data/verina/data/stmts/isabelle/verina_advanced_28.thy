(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_28,
  catalog title "longestConsecutive": an executable hash-set-style scan
  computes the length of the longest consecutive-integer streak in a
  duplicate-free integer list, together with its exhaustive sorted-sublist
  maximality contract. This file contains no proof.
*)

theory verina_advanced_28
  imports Main
begin

definition longestConsecutive_precond :: "int list \<Rightarrow> bool" where
  "longestConsecutive_precond nums \<longleftrightarrow> distinct nums"

definition longestConsecutive_set :: "int list \<Rightarrow> int set" where
  "longestConsecutive_set nums = set nums"

fun longestConsecutive_extend ::
    "int set \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "longestConsecutive_extend values current len 0 = len"
| "longestConsecutive_extend values current len (Suc fuel) =
    (if current + 1 \<in> values
     then longestConsecutive_extend values (current + 1) (Suc len) fuel
     else len)"

definition longestConsecutive_step ::
    "int set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat" where
  "longestConsecutive_step values fuel maxLen x =
    (if x - 1 \<notin> values
     then max maxLen (longestConsecutive_extend values x 1 fuel)
     else maxLen)"

definition longestConsecutive :: "int list \<Rightarrow> nat" where
  "longestConsecutive nums =
    (let values = longestConsecutive_set nums
     in foldl
          (longestConsecutive_step values (length nums))
          0 nums)"

definition isConsecutive :: "int list \<Rightarrow> bool" where
  "isConsecutive seq \<longleftrightarrow>
    seq = [] \<or>
    list_all
      (\<lambda>(x, i). x = int i + hd seq)
      (zip seq [0..<length seq])"

definition lean_extract ::
    "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "lean_extract xs start stop =
    take (stop - start) (drop start xs)"

definition consecutive_sublist_lens :: "int list \<Rightarrow> nat list" where
  "consecutive_sublist_lens nums =
    (let sorted_nums = sort nums;
         sublists =
           concat
             (map
               (\<lambda>start.
                 map
                   (\<lambda>len.
                     lean_extract sorted_nums start (start + len))
                   [0..<(length nums - start + 1)])
               [0..<length nums])
     in map length (filter isConsecutive sublists))"

definition longestConsecutive_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> bool" where
  "longestConsecutive_postcond nums result \<longleftrightarrow>
    (let consec_sublist_lens = consecutive_sublist_lens nums
     in (nums = [] \<longrightarrow> result = 0) \<and>
        (nums \<noteq> [] \<longrightarrow>
          result \<in> set consec_sublist_lens \<and>
          list_all (\<lambda>len. len \<le> result) consec_sublist_lens))"

theorem longestConsecutive_spec_satisfied:
  assumes "longestConsecutive_precond nums"
  shows
    "longestConsecutive_postcond nums (longestConsecutive nums)"
  sorry

end
