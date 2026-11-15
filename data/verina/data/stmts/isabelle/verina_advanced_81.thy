(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_81,
  catalog title "uniqueSorted": an executable program retains the first
  occurrence of each integer and insertion-sorts the result, with a contract
  requiring a permutation of the deduplicated input whose elements are
  pairwise nondecreasing. This file contains no proof.
*)

theory verina_advanced_81
  imports Main
begin

definition uniqueSorted_precond :: "int list \<Rightarrow> bool" where
  "uniqueSorted_precond arr \<longleftrightarrow> True"

fun uniqueSorted_insert :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "uniqueSorted_insert x [] = [x]"
| "uniqueSorted_insert x (head # tail) =
    (if x \<le> head
     then x # head # tail
     else head # uniqueSorted_insert x tail)"

fun uniqueSorted_insertionSort :: "int list \<Rightarrow> int list" where
  "uniqueSorted_insertionSort [] = []"
| "uniqueSorted_insertionSort (h # t) =
    uniqueSorted_insert h (uniqueSorted_insertionSort t)"

fun uniqueSorted_removeDupsAux ::
    "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list" where
  "uniqueSorted_removeDupsAux [] seen acc = rev acc"
| "uniqueSorted_removeDupsAux (h # t) seen acc =
    (if h \<in> set seen
     then uniqueSorted_removeDupsAux t seen acc
     else uniqueSorted_removeDupsAux t (h # seen) (h # acc))"

definition uniqueSorted_removeDups :: "int list \<Rightarrow> int list" where
  "uniqueSorted_removeDups xs = uniqueSorted_removeDupsAux xs [] []"

definition uniqueSorted :: "int list \<Rightarrow> int list" where
  "uniqueSorted arr =
    uniqueSorted_insertionSort (uniqueSorted_removeDups arr)"

fun uniqueSorted_pairwise_le :: "int list \<Rightarrow> bool" where
  "uniqueSorted_pairwise_le [] = True"
| "uniqueSorted_pairwise_le (h # t) =
    (list_all (\<lambda>x. h \<le> x) t \<and> uniqueSorted_pairwise_le t)"

definition uniqueSorted_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "uniqueSorted_postcond arr result \<longleftrightarrow>
    (\<forall>z. count_list (remdups arr) z = count_list result z) \<and>
    uniqueSorted_pairwise_le result"

theorem uniqueSorted_spec_satisfied:
  assumes "uniqueSorted_precond arr"
  shows "uniqueSorted_postcond arr (uniqueSorted arr)"
  sorry

end
