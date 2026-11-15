(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_78,
  catalog title "twoSum": an executable left-to-right search returns the
  increasing indices of the unique pair of integers whose sum is the target,
  together with its exact precondition and postcondition. This file contains
  no proof.
*)

theory verina_advanced_78
  imports Main
begin

definition intList_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "intList_getBang nums i =
    (if i < length nums then nums ! i else 0)"

definition twoSum_pairwiseSums :: "int list \<Rightarrow> int list" where
  "twoSum_pairwiseSums nums =
    concat
      (map
        (\<lambda>i.
          map
            (\<lambda>y. intList_getBang nums i + y)
            (drop (i + 1) nums))
        [0..<length nums])"

definition twoSum_precond :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "twoSum_precond nums target \<longleftrightarrow>
    length nums > 1 \<and>
    count_list (twoSum_pairwiseSums nums) target = 1"

fun findComplement_aux ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow>
      nat \<Rightarrow> nat option" where
  "findComplement_aux [] target i x j = None"
| "findComplement_aux (y # ys) target i x j =
    (if x + y = target
     then Some (i + j + 1)
     else findComplement_aux ys target i x (j + 1))"

definition findComplement ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow>
      nat option" where
  "findComplement nums target i x =
    findComplement_aux nums target i x 0"

fun twoSumAux :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "twoSumAux [] target i = (0, 0)"
| "twoSumAux (x # xs) target i =
    (case findComplement xs target i x of
       Some j \<Rightarrow> (i, j)
     | None \<Rightarrow> twoSumAux xs target (i + 1))"

definition twoSum :: "int list \<Rightarrow> int \<Rightarrow> nat \<times> nat" where
  "twoSum nums target = twoSumAux nums target 0"

definition twoSum_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "twoSum_postcond nums target result \<longleftrightarrow>
    (let i = fst result;
         j = snd result
     in i < j \<and>
        i < length nums \<and>
        j < length nums \<and>
        intList_getBang nums i + intList_getBang nums j = target)"

theorem twoSum_spec_satisfied:
  assumes "twoSum_precond nums target"
  shows "twoSum_postcond nums target (twoSum nums target)"
  sorry

end
