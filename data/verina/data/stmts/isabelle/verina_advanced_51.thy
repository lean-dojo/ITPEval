(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_51,
  catalog title "mergeSorted": an executable head-comparison merge combines
  two pairwise nondecreasing integer lists into a pairwise nondecreasing
  permutation of their concatenation. This file contains no proof.
*)

theory verina_advanced_51
  imports Main
begin

fun mergeSorted_pairwise_le :: "int list \<Rightarrow> bool" where
  "mergeSorted_pairwise_le [] = True"
| "mergeSorted_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     mergeSorted_pairwise_le xs)"

definition mergeSorted_precond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "mergeSorted_precond a b \<longleftrightarrow>
    mergeSorted_pairwise_le a \<and>
    mergeSorted_pairwise_le b"

fun mergeSortedAux :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "mergeSortedAux [] ys = ys"
| "mergeSortedAux xs [] = xs"
| "mergeSortedAux (x # xs) (y # ys) =
    (if x \<le> y
     then x # mergeSortedAux xs (y # ys)
     else y # mergeSortedAux (x # xs) ys)"

definition mergeSorted ::
    "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "mergeSorted a b = mergeSortedAux a b"

definition mergeSorted_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> bool" where
  "mergeSorted_postcond a b result \<longleftrightarrow>
    mergeSorted_pairwise_le result \<and>
    (\<forall>z. count_list result z = count_list (a @ b) z)"

theorem mergeSorted_spec_satisfied:
  assumes "mergeSorted_precond a b"
  shows "mergeSorted_postcond a b (mergeSorted a b)"
  sorry

end
