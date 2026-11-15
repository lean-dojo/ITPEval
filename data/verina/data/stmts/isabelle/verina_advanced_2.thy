(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_2,
  catalog title "LongestCommonSubsequence": an executable row-major dynamic
  program computes the longest common subsequence length of two integer
  sequences, with its precondition and subsequence-maximality postcondition.
  This file contains no proof.
*)

theory verina_advanced_2
  imports Main
begin

definition LongestCommonSubsequence_precond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "LongestCommonSubsequence_precond a b \<longleftrightarrow> True"

definition intMax :: "int \<Rightarrow> int \<Rightarrow> int" where
  "intMax x y = (if x < y then y else x)"

definition list_getBang :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a" where
  "list_getBang dflt xs i =
    (if i < length xs then xs ! i else dflt)"

definition list_setBang :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

definition lcs_get :: "int list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "lcs_get dp i j =
    list_getBang 0 (list_getBang [] dp i) j"

definition lcs_set ::
    "int list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list list" where
  "lcs_set dp i j value =
    list_setBang dp i
      (list_setBang (list_getBang [] dp i) j value)"

definition lcs_cell ::
    "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      int list list \<Rightarrow> int list list" where
  "lcs_cell a b i j dp =
    (if i = 0 \<or> j = 0 then dp
     else if list_getBang 0 a (i - 1) = list_getBang 0 b (j - 1)
     then lcs_set dp i j (lcs_get dp (i - 1) (j - 1) + 1)
     else lcs_set dp i j
       (intMax (lcs_get dp (i - 1) j) (lcs_get dp i (j - 1))))"

definition lcs_row ::
    "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow>
      int list list \<Rightarrow> int list list" where
  "lcs_row a b i dp =
    foldl (\<lambda>table j. lcs_cell a b i j table)
      dp [0..<length b + 1]"

definition LongestCommonSubsequence ::
    "int list \<Rightarrow> int list \<Rightarrow> int" where
  "LongestCommonSubsequence a b =
    (let initial =
       replicate (length a + 1) (replicate (length b + 1) 0);
         dp =
       foldl (\<lambda>table i. lcs_row a b i table)
         initial [0..<length a + 1]
     in lcs_get dp (length a) (length b))"

definition allSubseq :: "int list \<Rightarrow> int list list" where
  "allSubseq arr =
    map rev
      (foldl
        (\<lambda>acc x. acc @ map (\<lambda>sub. x # sub) acc)
        [[]] arr)"

definition LongestCommonSubsequence_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> bool" where
  "LongestCommonSubsequence_postcond a b result \<longleftrightarrow>
    (let subseqA = allSubseq a;
         subseqB = allSubseq b;
         commonSubseqLens =
           map (\<lambda>l. int (length l))
             (filter (\<lambda>l. l \<in> set subseqB) subseqA)
     in result \<in> set commonSubseqLens \<and>
        list_all (\<lambda>k. k \<le> result) commonSubseqLens)"

theorem LongestCommonSubsequence_spec_satisfied:
  assumes "LongestCommonSubsequence_precond a b"
  shows
    "LongestCommonSubsequence_postcond
      a b (LongestCommonSubsequence a b)"
  sorry

end
