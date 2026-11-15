(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_73,
  catalog title "smallestMissing": an executable recursive search scans a
  strictly increasing list of natural numbers and returns the least natural
  number absent from the list. This file contains no proof.
*)

theory verina_advanced_73
  imports Main
begin

fun smallestMissing_pairwise_lt :: "nat list \<Rightarrow> bool" where
  "smallestMissing_pairwise_lt [] = True"
| "smallestMissing_pairwise_lt (x # xs) =
    (list_all (\<lambda>y. x < y) xs \<and>
     smallestMissing_pairwise_lt xs)"

definition smallestMissing_precond :: "nat list \<Rightarrow> bool" where
  "smallestMissing_precond l \<longleftrightarrow>
    smallestMissing_pairwise_lt l"

fun smallestMissing_search :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "smallestMissing_search [] n = n"
| "smallestMissing_search (x # xs) n =
    (if x = n
     then smallestMissing_search xs (n + 1)
     else if x > n
     then n
     else smallestMissing_search xs n)"

definition smallestMissing :: "nat list \<Rightarrow> nat" where
  "smallestMissing l = smallestMissing_search l 0"

definition smallestMissing_postcond ::
    "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "smallestMissing_postcond l result \<longleftrightarrow>
    result \<notin> set l \<and>
    (\<forall>candidate<result. candidate \<in> set l)"

theorem smallestMissing_spec_satisfied:
  assumes "smallestMissing_precond l"
  shows "smallestMissing_postcond l (smallestMissing l)"
  sorry

end
