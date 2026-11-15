(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_80,
  catalog title "twoSum": a fuel-bounded executable array search returns two
  increasing indices whose integer values sum to the target, under the exact
  existence-and-uniqueness precondition and postcondition. This file contains
  no proof.
*)

theory verina_advanced_80
  imports Main
begin

definition intList_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "intList_getBang nums i =
    (if i < length nums then nums ! i else 0)"

definition natList_getBang :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "natList_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition twoSum_matchingSecondIndices ::
    "int list \<Rightarrow> int \<Rightarrow> nat list" where
  "twoSum_matchingSecondIndices nums target =
    concat
      (map
        (\<lambda>i.
          filter
            (\<lambda>j. intList_getBang nums i + intList_getBang nums j = target)
            [0..<i])
        [0..<length nums])"

definition twoSum_precond :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "twoSum_precond nums target \<longleftrightarrow>
    2 \<le> length nums \<and>
    list_ex
      (\<lambda>i.
        list_ex
          (\<lambda>j. intList_getBang nums i + intList_getBang nums j = target)
          [0..<i])
      [0..<length nums] \<and>
    length (twoSum_matchingSecondIndices nums target) = 1"

fun twoSum_findIndices ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
      \<Rightarrow> nat list" where
  "twoSum_findIndices nums target i j 0 = []"
| "twoSum_findIndices nums target i j (Suc fuel) =
    (if i \<ge> length nums
     then []
     else if j \<ge> length nums
          then twoSum_findIndices nums target (i + 1) (i + 2) fuel
          else if intList_getBang nums i + intList_getBang nums j = target
               then [i, j]
               else twoSum_findIndices nums target i (j + 1) fuel)"

definition twoSum :: "int list \<Rightarrow> int \<Rightarrow> nat list" where
  "twoSum nums target =
    twoSum_findIndices nums target 0 1 (length nums * length nums)"

definition twoSum_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> nat list \<Rightarrow> bool" where
  "twoSum_postcond nums target result \<longleftrightarrow>
    length result = 2 \<and>
    natList_getBang result 0 < length nums \<and>
    natList_getBang result 1 < length nums \<and>
    natList_getBang result 0 < natList_getBang result 1 \<and>
    intList_getBang nums (natList_getBang result 0) +
      intList_getBang nums (natList_getBang result 1) = target"

theorem twoSum_spec_satisfied:
  assumes "twoSum_precond nums target"
  shows "twoSum_postcond nums target (twoSum nums target)"
  sorry

end
