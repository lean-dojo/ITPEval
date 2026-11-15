(*
  Statement-only formalization of VERINA corpus artifact verina_basic_33
  (verina__isabelle__verina_basic_33), catalog title
  "smallestMissingNumber": an executable recursive scan of a pairwise
  nondecreasing natural-number list returns the least natural number absent
  from the list, together with its precondition, postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_33
  imports Main
begin

fun smallestMissingNumber_pairwise_le :: "nat list \<Rightarrow> bool" where
  "smallestMissingNumber_pairwise_le [] = True"
| "smallestMissingNumber_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     smallestMissingNumber_pairwise_le xs)"

definition smallestMissingNumber_precond :: "nat list \<Rightarrow> bool" where
  "smallestMissingNumber_precond s \<longleftrightarrow>
    smallestMissingNumber_pairwise_le s"

fun smallestMissingNumber_findMissing ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "smallestMissingNumber_findMissing v [] = v"
| "smallestMissingNumber_findMissing v (x # xs) =
    (if x > v
     then v
     else if x = v
          then smallestMissingNumber_findMissing (v + 1) xs
          else smallestMissingNumber_findMissing v xs)"

definition smallestMissingNumber :: "nat list \<Rightarrow> nat" where
  "smallestMissingNumber s =
    smallestMissingNumber_findMissing 0 s"

definition smallestMissingNumber_postcond ::
    "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "smallestMissingNumber_postcond s result \<longleftrightarrow>
    result \<notin> set s \<and>
    (\<forall>k<result. k \<in> set s)"

theorem smallestMissingNumber_spec_satisfied:
  assumes "smallestMissingNumber_precond s"
  shows "smallestMissingNumber_postcond s (smallestMissingNumber s)"
  sorry

end
