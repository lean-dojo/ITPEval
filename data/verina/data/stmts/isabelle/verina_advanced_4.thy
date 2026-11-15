(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_4,
  catalog title "LongestIncreasingSubsequence": an executable row-major
  dynamic program computes the length of a longest strictly increasing
  subsequence of an integer array, with its precondition and maximality
  contract. This file contains no proof.
*)

theory verina_advanced_4
  imports Main
begin

definition LongestIncreasingSubsequence_precond ::
    "int list \<Rightarrow> bool" where
  "LongestIncreasingSubsequence_precond a \<longleftrightarrow> True"

definition intMax :: "int \<Rightarrow> int \<Rightarrow> int" where
  "intMax x y = (if x < y then y else x)"

definition list_getBang ::
    "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a" where
  "list_getBang dflt xs i =
    (if i < length xs then xs ! i else dflt)"

definition list_setBang ::
    "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

definition LongestIncreasingSubsequence_cell ::
    "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> nat
      \<Rightarrow> int list" where
  "LongestIncreasingSubsequence_cell a i dp j =
    (if list_getBang 0 a j < list_getBang 0 a i
     then
       list_setBang dp i
         (intMax (list_getBang 0 dp i) (list_getBang 0 dp j + 1))
     else dp)"

definition LongestIncreasingSubsequence_row ::
    "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int list" where
  "LongestIncreasingSubsequence_row a dp i =
    foldl (LongestIncreasingSubsequence_cell a i) dp [0..<i]"

definition LongestIncreasingSubsequence :: "int list \<Rightarrow> int" where
  "LongestIncreasingSubsequence a =
    (let n = length a;
         initial = replicate n 1;
         dp =
           foldl (LongestIncreasingSubsequence_row a)
             initial [1..<n]
     in case dp of
          [] \<Rightarrow> 0
        | _ \<Rightarrow> foldl intMax 0 dp)"

definition LongestIncreasingSubsequence_allSubseq ::
    "int list \<Rightarrow> int list list" where
  "LongestIncreasingSubsequence_allSubseq a =
    map rev
      (foldl
        (\<lambda>acc x. acc @ map (\<lambda>sub. x # sub) acc)
        [[]] a)"

fun LongestIncreasingSubsequence_pairwiseLess ::
    "int list \<Rightarrow> bool" where
  "LongestIncreasingSubsequence_pairwiseLess [] = True"
| "LongestIncreasingSubsequence_pairwiseLess (x # xs) =
    (list_all (\<lambda>y. x < y) xs \<and>
     LongestIncreasingSubsequence_pairwiseLess xs)"

definition LongestIncreasingSubsequence_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "LongestIncreasingSubsequence_postcond a result \<longleftrightarrow>
    (let allSubseq = LongestIncreasingSubsequence_allSubseq a;
         increasingSubseqLens =
           map (\<lambda>subseq. int (length subseq))
             (filter LongestIncreasingSubsequence_pairwiseLess allSubseq)
     in result \<in> set increasingSubseqLens \<and>
        list_all (\<lambda>subseqLen. subseqLen \<le> result)
          increasingSubseqLens)"

theorem LongestIncreasingSubsequence_spec_satisfied:
  assumes "LongestIncreasingSubsequence_precond a"
  shows
    "LongestIncreasingSubsequence_postcond
      a (LongestIncreasingSubsequence a)"
  sorry

end
