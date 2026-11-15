(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_33,
  catalog title "longestIncreasingSubsequence": an executable take-or-skip
  search computes the length of a longest strictly increasing subsequence of
  an integer list, together with its precondition and maximality contract.
  This file contains no proof.
*)

theory verina_advanced_33
  imports Main
begin

definition longestIncreasingSubsequence_precond ::
    "int list \<Rightarrow> bool" where
  "longestIncreasingSubsequence_precond nums \<longleftrightarrow> True"

definition longestIncreasingSubsequence_max2 ::
    "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "longestIncreasingSubsequence_max2 a b =
    (if a > b then a else b)"

fun longestIncreasingSubsequence_listLength ::
    "int list \<Rightarrow> nat" where
  "longestIncreasingSubsequence_listLength [] = 0"
| "longestIncreasingSubsequence_listLength (x # xs) =
    1 + longestIncreasingSubsequence_listLength xs"

fun longestIncreasingSubsequence_helper ::
    "int list \<Rightarrow> int option \<Rightarrow> nat" where
  "longestIncreasingSubsequence_helper [] prev = 0"
| "longestIncreasingSubsequence_helper (h # t) prev =
    (let canTake =
       (case prev of None \<Rightarrow> True | Some p \<Rightarrow> p < h);
         withTake =
       (if canTake
        then 1 + longestIncreasingSubsequence_helper t (Some h)
        else 0);
         withoutTake = longestIncreasingSubsequence_helper t prev
     in longestIncreasingSubsequence_max2 withTake withoutTake)"

definition longestIncreasingSubsequence :: "int list \<Rightarrow> nat" where
  "longestIncreasingSubsequence nums =
    longestIncreasingSubsequence_helper nums None"

definition longestIncreasingSubsequence_allSubseq ::
    "int list \<Rightarrow> int list list" where
  "longestIncreasingSubsequence_allSubseq nums =
    map rev
      (foldl
        (\<lambda>acc x. acc @ map (\<lambda>sub. x # sub) acc)
        [[]] nums)"

fun longestIncreasingSubsequence_pairwiseLess ::
    "int list \<Rightarrow> bool" where
  "longestIncreasingSubsequence_pairwiseLess [] = True"
| "longestIncreasingSubsequence_pairwiseLess (x # xs) =
    (list_all (\<lambda>y. x < y) xs \<and>
     longestIncreasingSubsequence_pairwiseLess xs)"

definition longestIncreasingSubsequence_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> bool" where
  "longestIncreasingSubsequence_postcond nums result \<longleftrightarrow>
    (let allSubseq = longestIncreasingSubsequence_allSubseq nums;
         increasingSubseqLens =
           map length
             (filter longestIncreasingSubsequence_pairwiseLess allSubseq)
     in result \<in> set increasingSubseqLens \<and>
        list_all (\<lambda>subseqLen. subseqLen \<le> result)
          increasingSubseqLens)"

theorem longestIncreasingSubsequence_spec_satisfied:
  assumes "longestIncreasingSubsequence_precond nums"
  shows
    "longestIncreasingSubsequence_postcond
      nums (longestIncreasingSubsequence nums)"
  sorry

end
