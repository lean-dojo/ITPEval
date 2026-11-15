(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_34,
  catalog title "longestIncreasingSubsequence": an executable patience-sorting
  program with binary search computes an integer length, with its trivial
  precondition and longest strictly increasing subsequence postcondition.
  This file contains no proof.
*)

theory verina_advanced_34
  imports Main
begin

definition longestIncreasingSubsequence_precond ::
    "int list \<Rightarrow> bool" where
  "longestIncreasingSubsequence_precond nums \<longleftrightarrow> True"

definition list_getBang ::
    "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a" where
  "list_getBang dflt xs i =
    (if i < length xs then xs ! i else dflt)"

definition list_setBang ::
    "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

fun binarySearchLeft_fuel ::
    "nat \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat
      \<Rightarrow> nat" where
  "binarySearchLeft_fuel 0 sub num left right = left"
| "binarySearchLeft_fuel (Suc fuel) sub num left right =
    (if left < right
     then
       (let mid = (left + right) div 2;
            value = list_getBang 0 sub mid
        in if value = num
           then binarySearchLeft_fuel fuel sub num left mid
           else if value < num
                then binarySearchLeft_fuel fuel sub num (mid + 1) right
                else binarySearchLeft_fuel fuel sub num left mid)
     else left)"

definition binarySearchLeft ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
    where
  "binarySearchLeft sub num left right =
    binarySearchLeft_fuel (right - left) sub num left right"

definition longestIncreasingSubsequence_step ::
    "int list \<Rightarrow> int \<Rightarrow> int list" where
  "longestIncreasingSubsequence_step sub num =
    (if num > list_getBang 0 sub (length sub - 1)
     then sub @ [num]
     else
       (let left = binarySearchLeft sub num 0 (length sub - 1)
        in list_setBang sub left num))"

definition longestIncreasingSubsequence ::
    "int list \<Rightarrow> int" where
  "longestIncreasingSubsequence nums =
    (if nums = []
     then 0
     else
       int
         (length
           (foldl longestIncreasingSubsequence_step
             [hd nums] (tl nums))))"

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
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "longestIncreasingSubsequence_postcond nums result \<longleftrightarrow>
    (let allSubseq = longestIncreasingSubsequence_allSubseq nums;
         increasingSubseqLens =
           map (\<lambda>subseq. int (length subseq))
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
