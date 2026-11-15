(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_32,
  catalog title "longestIncreasingSubsequence": an executable dynamic program
  computes the length of a longest strictly increasing subsequence of an
  integer list, with its precondition and subsequence-maximality postcondition.
  This file contains no proof.
*)

theory verina_advanced_32
  imports Main
begin

definition longestIncreasingSubsequence_precond ::
    "int list \<Rightarrow> bool" where
  "longestIncreasingSubsequence_precond numbers \<longleftrightarrow> True"

fun longestIncreasingSubsequence_findMaxLength ::
    "nat list \<Rightarrow> nat" where
  "longestIncreasingSubsequence_findMaxLength [] = 0"
| "longestIncreasingSubsequence_findMaxLength (x # xs) =
    (let maxRest = longestIncreasingSubsequence_findMaxLength xs
     in if x > maxRest then x else maxRest)"

fun longestIncreasingSubsequence_findLengthEndingAtCurr ::
    "int \<Rightarrow> int list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "longestIncreasingSubsequence_findLengthEndingAtCurr currNum [] lengths best =
    best"
| "longestIncreasingSubsequence_findLengthEndingAtCurr currNum
      (prevVal # restVals) [] best =
    best"
| "longestIncreasingSubsequence_findLengthEndingAtCurr currNum
      (prevVal # restVals) (prevLen # restLens) best =
    (if prevVal < currNum
     then
       longestIncreasingSubsequence_findLengthEndingAtCurr
         currNum restVals restLens (max best prevLen)
     else
       longestIncreasingSubsequence_findLengthEndingAtCurr
         currNum restVals restLens best)"

fun longestIncreasingSubsequence_buildTables ::
    "int list \<Rightarrow> int list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "longestIncreasingSubsequence_buildTables [] prevNums lengths idx =
    longestIncreasingSubsequence_findMaxLength lengths"
| "longestIncreasingSubsequence_buildTables
      (currNum # restNums) prevNums lengths idx =
    (let bestPrevLen =
       longestIncreasingSubsequence_findLengthEndingAtCurr
         currNum prevNums lengths 0;
         currLength = bestPrevLen + 1
     in longestIncreasingSubsequence_buildTables
          restNums (prevNums @ [currNum]) (lengths @ [currLength]) (idx + 1))"

fun longestIncreasingSubsequence :: "int list \<Rightarrow> nat" where
  "longestIncreasingSubsequence [] = 0"
| "longestIncreasingSubsequence [x] = 1"
| "longestIncreasingSubsequence (first # next # rest) =
    longestIncreasingSubsequence_buildTables
      (next # rest) [first] [1] 1"

definition longestIncreasingSubsequence_allSubseq ::
    "int list \<Rightarrow> int list list" where
  "longestIncreasingSubsequence_allSubseq numbers =
    map rev
      (foldl
        (\<lambda>acc x. acc @ map (\<lambda>sub. x # sub) acc)
        [[]] numbers)"

fun longestIncreasingSubsequence_pairwiseLess ::
    "int list \<Rightarrow> bool" where
  "longestIncreasingSubsequence_pairwiseLess [] = True"
| "longestIncreasingSubsequence_pairwiseLess (x # xs) =
    (list_all (\<lambda>y. x < y) xs \<and>
     longestIncreasingSubsequence_pairwiseLess xs)"

definition longestIncreasingSubsequence_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> bool" where
  "longestIncreasingSubsequence_postcond numbers result \<longleftrightarrow>
    (let allSubseq = longestIncreasingSubsequence_allSubseq numbers;
         increasingSubseqLens =
           map length
             (filter longestIncreasingSubsequence_pairwiseLess allSubseq)
     in result \<in> set increasingSubseqLens \<and>
        list_all (\<lambda>subseqLen. subseqLen \<le> result)
          increasingSubseqLens)"

theorem longestIncreasingSubsequence_spec_satisfied:
  assumes "longestIncreasingSubsequence_precond numbers"
  shows
    "longestIncreasingSubsequence_postcond
      numbers (longestIncreasingSubsequence numbers)"
  sorry

end
