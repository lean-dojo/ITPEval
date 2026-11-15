(*
  Statement-only formalization of VERINA corpus artifact verina_basic_22
  (verina__isabelle__verina_basic_22), catalog title "dissimilarElements":
  an executable integer-array program returns the sorted duplicate-free
  symmetric difference of two arrays, together with its unconditional
  precondition, full postcondition, and final correctness proposition.
  This file contains no proof.
*)

theory verina_basic_22
  imports Main
begin

definition inArray :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "inArray a x \<longleftrightarrow> x \<in> set a"

definition dissimilarElements_precond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "dissimilarElements_precond a b \<longleftrightarrow> True"

definition dissimilarElements_collect ::
    "int list \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int list" where
  "dissimilarElements_collect other acc x =
    (if \<not> inArray other x
     then if x \<in> set acc then acc else x # acc
     else acc)"

fun dissimilarElements_insert ::
    "int \<Rightarrow> int list \<Rightarrow> int list" where
  "dissimilarElements_insert x [] = [x]"
| "dissimilarElements_insert x (y # ys) =
    (if x \<le> y
     then x # y # ys
     else y # dissimilarElements_insert x ys)"

fun dissimilarElements_sort :: "int list \<Rightarrow> int list" where
  "dissimilarElements_sort [] = []"
| "dissimilarElements_sort (x # xs) =
    dissimilarElements_insert x (dissimilarElements_sort xs)"

definition dissimilarElements ::
    "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "dissimilarElements a b =
    (let fromA =
       foldl (dissimilarElements_collect b) [] a;
         fromBoth =
       foldl (dissimilarElements_collect a) fromA b
     in dissimilarElements_sort fromBoth)"

fun dissimilarElements_pairwise_le :: "int list \<Rightarrow> bool" where
  "dissimilarElements_pairwise_le [] = True"
| "dissimilarElements_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     dissimilarElements_pairwise_le xs)"

definition dissimilarElements_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> bool" where
  "dissimilarElements_postcond a b result \<longleftrightarrow>
    list_all (\<lambda>x. inArray a x \<noteq> inArray b x) result \<and>
    dissimilarElements_pairwise_le result \<and>
    distinct result \<and>
    list_all
      (\<lambda>x. if x \<in> set b
        then x \<notin> set result
        else x \<in> set result)
      a \<and>
    list_all
      (\<lambda>x. if x \<in> set a
        then x \<notin> set result
        else x \<in> set result)
      b"

theorem dissimilarElements_spec_satisfied:
  assumes "dissimilarElements_precond a b"
  shows
    "dissimilarElements_postcond a b (dissimilarElements a b)"
  sorry

end
