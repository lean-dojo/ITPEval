(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_30,
  catalog title "longestIncreasingStreak": an executable accumulator-based
  scan computes the longest strictly increasing contiguous streak in an
  integer list, together with its complete maximality contract. This file
  contains no proof.
*)

theory verina_advanced_30
  imports Main
begin

definition longestIncreasingStreak_precond :: "int list \<Rightarrow> bool" where
  "longestIncreasingStreak_precond nums \<longleftrightarrow> True"

fun longestIncreasingStreak_aux ::
    "int list \<Rightarrow> int option \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "longestIncreasingStreak_aux [] prev currLen maxLen =
    max currLen maxLen"
| "longestIncreasingStreak_aux (x # xs) None currLen maxLen =
    longestIncreasingStreak_aux xs (Some x) 1 (max 1 maxLen)"
| "longestIncreasingStreak_aux (x # xs) (Some p) currLen maxLen =
    (if x > p
     then
       longestIncreasingStreak_aux
         xs (Some x) (currLen + 1) (max (currLen + 1) maxLen)
     else
       longestIncreasingStreak_aux
         xs (Some x) 1 (max currLen maxLen))"

definition longestIncreasingStreak :: "int list \<Rightarrow> nat" where
  "longestIncreasingStreak nums =
    longestIncreasingStreak_aux nums None 0 0"

definition longestIncreasingStreak_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "longestIncreasingStreak_getBang nums i =
    (if i < length nums then nums ! i else 0)"

definition longestIncreasingStreak_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> bool" where
  "longestIncreasingStreak_postcond nums result \<longleftrightarrow>
    (nums = [] \<longrightarrow> result = 0) \<and>
    (result > 0 \<longrightarrow>
      list_ex
        (\<lambda>start.
          start + result \<le> length nums \<and>
          list_all
            (\<lambda>i.
              longestIncreasingStreak_getBang nums (start + i) <
              longestIncreasingStreak_getBang nums (start + i + 1))
            [0..<(result - 1)] \<and>
          (start = 0 \<or>
            longestIncreasingStreak_getBang nums (start - 1) \<ge>
            longestIncreasingStreak_getBang nums start) \<and>
          (start + result = length nums \<or>
            longestIncreasingStreak_getBang nums (start + result - 1) \<ge>
            longestIncreasingStreak_getBang nums (start + result)))
        [0..<(length nums - result + 1)]) \<and>
    list_all
      (\<lambda>start.
        list_ex
          (\<lambda>i.
            start + i + 1 \<ge> length nums \<or>
            longestIncreasingStreak_getBang nums (start + i) \<ge>
            longestIncreasingStreak_getBang nums (start + i + 1))
          [0..<result])
      [0..<(length nums - result)]"

theorem longestIncreasingStreak_spec_satisfied:
  assumes "longestIncreasingStreak_precond nums"
  shows
    "longestIncreasingStreak_postcond
      nums (longestIncreasingStreak nums)"
  sorry

end
