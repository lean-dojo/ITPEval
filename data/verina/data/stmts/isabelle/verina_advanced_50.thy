(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_50,
  catalog title "mergeSorted": an executable indexed merge and suffix-draining
  program combines two pairwise nondecreasing natural-number arrays into a
  pairwise nondecreasing permutation of their concatenation. This file
  contains no proof.
*)

theory verina_advanced_50
  imports Main
begin

fun mergeSorted_pairwise_le :: "nat list \<Rightarrow> bool" where
  "mergeSorted_pairwise_le [] = True"
| "mergeSorted_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     mergeSorted_pairwise_le xs)"

definition mergeSorted_precond ::
    "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "mergeSorted_precond a1 a2 \<longleftrightarrow>
    mergeSorted_pairwise_le a1 \<and>
    mergeSorted_pairwise_le a2"

fun mergeLoop_remaining ::
    "nat list \<Rightarrow> nat list \<Rightarrow>
     nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
     nat \<times> nat \<times> nat list" where
  "mergeLoop_remaining [] ys i j result = (i, j, result)"
| "mergeLoop_remaining xs [] i j result = (i, j, result)"
| "mergeLoop_remaining (x # xs) (y # ys) i j result =
    (if x \<le> y
     then mergeLoop_remaining xs (y # ys) (i + 1) j (result @ [x])
     else mergeLoop_remaining (x # xs) ys i (j + 1) (result @ [y]))"

definition mergeLoop ::
    "nat list \<Rightarrow> nat list \<Rightarrow>
     nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
     nat \<times> nat \<times> nat list" where
  "mergeLoop a1 a2 i j result =
    mergeLoop_remaining (drop i a1) (drop j a2) i j result"

fun drain_remaining ::
    "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "drain_remaining [] result = result"
| "drain_remaining (x # xs) result =
    drain_remaining xs (result @ [x])"

definition drain ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "drain arr i result = drain_remaining (drop i arr) result"

definition mergeSorted ::
    "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "mergeSorted a1 a2 =
    (case mergeLoop a1 a2 0 0 [] of
       (i, j, result) \<Rightarrow> drain a2 j (drain a1 i result))"

definition mergeSorted_postcond ::
    "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "mergeSorted_postcond a1 a2 result \<longleftrightarrow>
    mergeSorted_pairwise_le result \<and>
    (\<forall>z. count_list result z = count_list (a1 @ a2) z)"

theorem mergeSorted_spec_satisfied:
  assumes "mergeSorted_precond a1 a2"
  shows "mergeSorted_postcond a1 a2 (mergeSorted a1 a2)"
  sorry

end
