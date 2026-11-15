(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_25,
  catalog title "lengthOfLIS": an executable dynamic-programming program
  computes the length of a longest strictly increasing subsequence of an
  integer list, together with its precondition and maximality contract. This
  file contains no proof.
*)

theory verina_advanced_25
  imports Main
begin

definition lengthOfLIS_precond :: "int list \<Rightarrow> bool" where
  "lengthOfLIS_precond nums \<longleftrightarrow> True"

definition list_getBang :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a" where
  "list_getBang dflt xs i =
    (if i < length xs then xs ! i else dflt)"

definition list_setBang :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

definition maxInArray :: "nat list \<Rightarrow> nat" where
  "maxInArray arr =
    foldl (\<lambda>a b. if a \<ge> b then a else b) 0 arr"

definition lengthOfLIS_cell ::
    "int list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "lengthOfLIS_cell nums i dp j =
    (if list_getBang 0 nums j < list_getBang 0 nums i \<and>
        list_getBang 0 dp j + 1 > list_getBang 0 dp i
     then list_setBang dp i (list_getBang 0 dp j + 1)
     else dp)"

definition lengthOfLIS_row ::
    "int list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "lengthOfLIS_row nums dp i =
    foldl (lengthOfLIS_cell nums i) dp [0..<i]"

definition lengthOfLIS :: "int list \<Rightarrow> nat" where
  "lengthOfLIS nums =
    (if nums = []
     then 0
     else
       (let n = length nums;
            initial = replicate n 1;
            dp = foldl (lengthOfLIS_row nums) initial [1..<n]
        in maxInArray dp))"

definition lengthOfLIS_allSubseq :: "int list \<Rightarrow> int list list" where
  "lengthOfLIS_allSubseq nums =
    map rev
      (foldl
        (\<lambda>acc x. acc @ map (\<lambda>sub. x # sub) acc)
        [[]] nums)"

fun lengthOfLIS_pairwiseLess :: "int list \<Rightarrow> bool" where
  "lengthOfLIS_pairwiseLess [] = True"
| "lengthOfLIS_pairwiseLess (x # xs) =
    (list_all (\<lambda>y. x < y) xs \<and>
     lengthOfLIS_pairwiseLess xs)"

definition lengthOfLIS_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> bool" where
  "lengthOfLIS_postcond nums result \<longleftrightarrow>
    (let allSubseq = lengthOfLIS_allSubseq nums;
         increasingSubseqLens =
           map length (filter lengthOfLIS_pairwiseLess allSubseq)
     in result \<in> set increasingSubseqLens \<and>
        list_all (\<lambda>k. k \<le> result) increasingSubseqLens)"

theorem lengthOfLIS_spec_satisfied:
  assumes "lengthOfLIS_precond nums"
  shows "lengthOfLIS_postcond nums (lengthOfLIS nums)"
  sorry

end
