(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_48,
  catalog title "mergeSort": an executable insertion-sort implementation
  inserts each integer into the recursively sorted tail and returns a pairwise
  nondecreasing permutation of the input. This file contains no proof.
*)

theory verina_advanced_48
  imports Main
begin

definition mergeSort_precond :: "int list \<Rightarrow> bool" where
  "mergeSort_precond list \<longleftrightarrow> True"

fun mergeSort_insert :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "mergeSort_insert x [] = [x]"
| "mergeSort_insert x (y # ys) =
    (if x \<le> y
     then x # y # ys
     else y # mergeSort_insert x ys)"

fun mergeSort_sort :: "int list \<Rightarrow> int list" where
  "mergeSort_sort [] = []"
| "mergeSort_sort (x # xs) =
    mergeSort_insert x (mergeSort_sort xs)"

definition mergeSort :: "int list \<Rightarrow> int list" where
  "mergeSort list = mergeSort_sort list"

fun mergeSort_pairwise_le :: "int list \<Rightarrow> bool" where
  "mergeSort_pairwise_le [] = True"
| "mergeSort_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     mergeSort_pairwise_le xs)"

definition mergeSort_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "mergeSort_postcond list result \<longleftrightarrow>
    mergeSort_pairwise_le result \<and>
    (\<forall>z. count_list list z = count_list result z)"

theorem mergeSort_spec_satisfied:
  assumes "mergeSort_precond list"
  shows "mergeSort_postcond list (mergeSort list)"
  sorry

end
