(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_16,
  catalog title "insertionSort": an executable insertion-sort program inserts
  each integer into the recursively sorted tail and returns a pairwise
  nondecreasing permutation of the input. This file contains no proof.
*)

theory verina_advanced_16
  imports Main
begin

definition insertionSort_precond :: "int list \<Rightarrow> bool" where
  "insertionSort_precond xs \<longleftrightarrow> True"

fun insertionSort_insert :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "insertionSort_insert x [] = [x]"
| "insertionSort_insert x (y # ys) =
    (if x \<le> y
     then x # y # ys
     else y # insertionSort_insert x ys)"

fun insertionSort :: "int list \<Rightarrow> int list" where
  "insertionSort [] = []"
| "insertionSort (x # xs) =
    insertionSort_insert x (insertionSort xs)"

fun insertionSort_pairwise_le :: "int list \<Rightarrow> bool" where
  "insertionSort_pairwise_le [] = True"
| "insertionSort_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     insertionSort_pairwise_le xs)"

definition insertionSort_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "insertionSort_postcond xs result \<longleftrightarrow>
    insertionSort_pairwise_le result \<and>
    (\<forall>z. count_list xs z = count_list result z)"

theorem insertionSort_spec_satisfied:
  assumes "insertionSort_precond xs"
  shows "insertionSort_postcond xs (insertionSort xs)"
  sorry

end
