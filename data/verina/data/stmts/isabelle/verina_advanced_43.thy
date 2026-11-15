(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_43,
  catalog title "maxStrength": an executable exhaustive subset computation
  returns the maximum product of a nonempty subset of an integer list,
  together with its nonempty-input precondition and maximality contract. This
  file contains no proof.
*)

theory verina_advanced_43
  imports Main
begin

definition maxStrength_precond :: "int list \<Rightarrow> bool" where
  "maxStrength_precond nums \<longleftrightarrow> nums \<noteq> []"

fun maxStrength_subsets :: "'a list \<Rightarrow> 'a list list" where
  "maxStrength_subsets [] = [[]]"
| "maxStrength_subsets (x # xs) =
    (let rest = maxStrength_subsets xs
     in rest @ map (\<lambda>subset. x # subset) rest)"

definition maxStrength_products :: "int list \<Rightarrow> int list" where
  "maxStrength_products nums =
    map (\<lambda>subset. foldl (\<lambda>acc x. acc * x) 1 subset)
      (filter (\<lambda>subset. subset \<noteq> []) (maxStrength_subsets nums))"

fun maxStrength_listMaxDefault :: "int \<Rightarrow> int list \<Rightarrow> int" where
  "maxStrength_listMaxDefault dflt [] = dflt"
| "maxStrength_listMaxDefault dflt (x # xs) = foldl max x xs"

definition maxStrength :: "int list \<Rightarrow> int" where
  "maxStrength nums =
    maxStrength_listMaxDefault (-1000000) (maxStrength_products nums)"

definition maxStrength_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "maxStrength_postcond nums result \<longleftrightarrow>
    (let products = maxStrength_products nums
     in result \<in> set products \<and>
        list_all (\<lambda>product. product \<le> result) products)"

theorem maxStrength_spec_satisfied:
  assumes "maxStrength_precond nums"
  shows "maxStrength_postcond nums (maxStrength nums)"
  sorry

end
