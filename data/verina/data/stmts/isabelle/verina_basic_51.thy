(*
  Statement-only formalization of VERINA corpus artifact verina_basic_51
  (verina__isabelle__verina_basic_51), catalog title "BinarySearch": an
  executable binary-search loop returns the lower-bound insertion index in a
  pairwise nondecreasing integer array, together with its precondition,
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_51
  imports Main
begin

fun BinarySearch_pairwise_le :: "int list \<Rightarrow> bool" where
  "BinarySearch_pairwise_le [] = True"
| "BinarySearch_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     BinarySearch_pairwise_le xs)"

definition BinarySearch_precond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "BinarySearch_precond a key \<longleftrightarrow>
    BinarySearch_pairwise_le a"

definition binarySearch_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "binarySearch_getBang a i =
    (if i < length a then a ! i else 0)"

partial_function (tailrec) binarySearchLoop ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "binarySearchLoop a key lo hi =
    (if lo < hi then
       let mid = (lo + hi) div 2
       in if binarySearch_getBang a mid < key
          then binarySearchLoop a key (mid + 1) hi
          else binarySearchLoop a key lo mid
     else lo)"

definition BinarySearch :: "int list \<Rightarrow> int \<Rightarrow> nat" where
  "BinarySearch a key =
    binarySearchLoop a key 0 (length a)"

definition BinarySearch_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool" where
  "BinarySearch_postcond a key result \<longleftrightarrow>
    result \<le> length a \<and>
    list_all (\<lambda>x. x < key) (take result a) \<and>
    list_all (\<lambda>x. x \<ge> key) (drop result a)"

theorem BinarySearch_spec_satisfied:
  assumes "BinarySearch_precond a key"
  shows "BinarySearch_postcond a key (BinarySearch a key)"
  sorry

end
