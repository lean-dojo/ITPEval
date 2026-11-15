(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_49,
  catalog title "mergeSortedLists": an executable merge combines two pairwise
  nondecreasing integer lists into a pairwise nondecreasing permutation of
  their concatenation. This file contains no proof.
*)

theory verina_advanced_49
  imports Main
begin

fun mergeSortedLists_pairwise_le :: "int list \<Rightarrow> bool" where
  "mergeSortedLists_pairwise_le [] = True"
| "mergeSortedLists_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     mergeSortedLists_pairwise_le xs)"

definition mergeSortedLists_precond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "mergeSortedLists_precond arr1 arr2 \<longleftrightarrow>
    mergeSortedLists_pairwise_le arr1 \<and>
    mergeSortedLists_pairwise_le arr2"

fun mergeSortedLists_merge ::
    "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "mergeSortedLists_merge [] ys = ys"
| "mergeSortedLists_merge xs [] = xs"
| "mergeSortedLists_merge (x # xt) (y # yt) =
    (if x \<le> y
     then x # mergeSortedLists_merge xt (y # yt)
     else y # mergeSortedLists_merge (x # xt) yt)"

definition mergeSortedLists ::
    "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "mergeSortedLists arr1 arr2 =
    mergeSortedLists_merge arr1 arr2"

definition mergeSortedLists_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> bool" where
  "mergeSortedLists_postcond arr1 arr2 result \<longleftrightarrow>
    mergeSortedLists_pairwise_le result \<and>
    (\<forall>z. count_list (arr1 @ arr2) z = count_list result z)"

theorem mergeSortedLists_spec_satisfied:
  assumes "mergeSortedLists_precond arr1 arr2"
  shows
    "mergeSortedLists_postcond
      arr1 arr2 (mergeSortedLists arr1 arr2)"
  sorry

end
