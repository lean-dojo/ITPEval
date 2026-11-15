(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_24,
  catalog title "lengthOfLIS": an executable integer-list program computes
  patience-sorting tails for the length of a longest strictly increasing
  subsequence, together with its precondition and maximality contract. This
  file contains no proof.
*)

theory verina_advanced_24
  imports Main
begin

definition lengthOfLIS_precond :: "int list \<Rightarrow> bool" where
  "lengthOfLIS_precond nums \<longleftrightarrow> True"

fun lengthOfLIS_replace ::
    "int \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list" where
  "lengthOfLIS_replace x [] acc = rev acc @ [x]"
| "lengthOfLIS_replace x (y # ys) acc =
    (if x \<le> y
     then rev acc @ (x # ys)
     else lengthOfLIS_replace x ys (y # acc))"

definition lengthOfLIS_helper ::
    "int list \<Rightarrow> int \<Rightarrow> int list" where
  "lengthOfLIS_helper dp x = lengthOfLIS_replace x dp []"

definition lengthOfLIS :: "int list \<Rightarrow> int" where
  "lengthOfLIS nums =
    int (length (foldl lengthOfLIS_helper [] nums))"

fun lengthOfLIS_strictlyIncreasing :: "int list \<Rightarrow> bool" where
  "lengthOfLIS_strictlyIncreasing [] = True"
| "lengthOfLIS_strictlyIncreasing [x] = True"
| "lengthOfLIS_strictlyIncreasing (x # y # rest) =
    (x < y \<and> lengthOfLIS_strictlyIncreasing (y # rest))"

fun lengthOfLIS_subsequences :: "int list \<Rightarrow> int list list" where
  "lengthOfLIS_subsequences [] = [[]]"
| "lengthOfLIS_subsequences (x # xs) =
    (let rest = lengthOfLIS_subsequences xs
     in rest @ map (\<lambda>r. x # r) rest)"

definition lengthOfLIS_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "lengthOfLIS_postcond nums result \<longleftrightarrow>
    (let allIncreasing =
       filter lengthOfLIS_strictlyIncreasing
         (lengthOfLIS_subsequences nums)
     in list_ex (\<lambda>l. int (length l) = result) allIncreasing \<and>
        list_all (\<lambda>l. int (length l) \<le> result) allIncreasing)"

theorem lengthOfLIS_spec_satisfied:
  assumes "lengthOfLIS_precond nums"
  shows "lengthOfLIS_postcond nums (lengthOfLIS nums)"
  sorry

end
