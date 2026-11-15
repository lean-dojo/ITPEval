(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_17,
  catalog title "insertionSort": an executable insertion-sort program inserts
  each integer into the recursively sorted tail and returns a pairwise
  nondecreasing permutation of the input. This file contains no proof.
*)

theory verina_advanced_17
  imports Main
begin

definition insertionSort_precond :: "int list \<Rightarrow> bool" where
  "insertionSort_precond l \<longleftrightarrow> True"

fun insertElement :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "insertElement x [] = [x]"
| "insertElement x (y # ys) =
    (if x \<le> y
     then x # y # ys
     else y # insertElement x ys)"

fun sortList :: "int list \<Rightarrow> int list" where
  "sortList [] = []"
| "sortList (x # xs) = insertElement x (sortList xs)"

definition insertionSort :: "int list \<Rightarrow> int list" where
  "insertionSort l = (let result = sortList l in result)"

fun insertionSort_pairwise_le :: "int list \<Rightarrow> bool" where
  "insertionSort_pairwise_le [] = True"
| "insertionSort_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     insertionSort_pairwise_le xs)"

definition insertionSort_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "insertionSort_postcond l result \<longleftrightarrow>
    insertionSort_pairwise_le result \<and>
    (\<forall>z. count_list l z = count_list result z)"

theorem insertionSort_spec_satisfied:
  assumes "insertionSort_precond l"
  shows "insertionSort_postcond l (insertionSort l)"
  sorry

end
