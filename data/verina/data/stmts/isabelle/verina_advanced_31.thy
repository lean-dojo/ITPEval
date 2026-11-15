(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_31,
  catalog title "longestIncreasingSubseqLength": an executable exhaustive
  subsequence search computes the length of a longest strictly increasing
  subsequence of an integer list, together with its precondition and
  maximality contract. This file contains no proof.
*)

theory verina_advanced_31
  imports Main
begin

definition longestIncreasingSubseqLength_precond ::
    "int list \<Rightarrow> bool" where
  "longestIncreasingSubseqLength_precond xs \<longleftrightarrow> True"

fun longestIncreasingSubseqLength_subsequences ::
    "'a list \<Rightarrow> 'a list list" where
  "longestIncreasingSubseqLength_subsequences [] = [[]]"
| "longestIncreasingSubseqLength_subsequences (x # xs) =
    (let subs = longestIncreasingSubseqLength_subsequences xs
     in subs @ map (\<lambda>s. x # s) subs)"

fun longestIncreasingSubseqLength_isStrictlyIncreasing ::
    "int list \<Rightarrow> bool" where
  "longestIncreasingSubseqLength_isStrictlyIncreasing [] = True"
| "longestIncreasingSubseqLength_isStrictlyIncreasing [x] = True"
| "longestIncreasingSubseqLength_isStrictlyIncreasing (x # y # rest) =
    (if x < y
     then longestIncreasingSubseqLength_isStrictlyIncreasing (y # rest)
     else False)"

definition longestIncreasingSubseqLength :: "int list \<Rightarrow> nat" where
  "longestIncreasingSubseqLength xs =
    (let subs = longestIncreasingSubseqLength_subsequences xs;
         increasing =
           filter longestIncreasingSubseqLength_isStrictlyIncreasing subs
     in foldl (\<lambda>acc s. max acc (length s)) 0 increasing)"

definition longestIncreasingSubseqLength_allSubseq ::
    "int list \<Rightarrow> int list list" where
  "longestIncreasingSubseqLength_allSubseq xs =
    map rev
      (foldl
        (\<lambda>acc x. acc @ map (\<lambda>sub. x # sub) acc)
        [[]] xs)"

fun longestIncreasingSubseqLength_pairwiseLess ::
    "int list \<Rightarrow> bool" where
  "longestIncreasingSubseqLength_pairwiseLess [] = True"
| "longestIncreasingSubseqLength_pairwiseLess (x # xs) =
    (list_all (\<lambda>y. x < y) xs \<and>
     longestIncreasingSubseqLength_pairwiseLess xs)"

definition longestIncreasingSubseqLength_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> bool" where
  "longestIncreasingSubseqLength_postcond xs result \<longleftrightarrow>
    (let allSubseq = longestIncreasingSubseqLength_allSubseq xs;
         increasingSubseqLens =
           map length
             (filter longestIncreasingSubseqLength_pairwiseLess allSubseq)
     in result \<in> set increasingSubseqLens \<and>
        list_all (\<lambda>k. k \<le> result) increasingSubseqLens)"

theorem longestIncreasingSubseqLength_spec_satisfied:
  assumes "longestIncreasingSubseqLength_precond xs"
  shows
    "longestIncreasingSubseqLength_postcond
      xs (longestIncreasingSubseqLength xs)"
  sorry

end
