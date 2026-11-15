(*
  Statement-only formalization of VERINA corpus artifact verina_basic_2,
  catalog title "findSmallest": an executable natural-number array program
  returns no value exactly for an empty array and otherwise returns its
  smallest member, together with its trivial precondition and correctness
  contract. This file contains no proof.
*)

theory verina_basic_2
  imports Main
begin

definition findSmallest_precond :: "nat list \<Rightarrow> bool" where
  "findSmallest_precond s \<longleftrightarrow> True"

fun findSmallest :: "nat list \<Rightarrow> nat option" where
  "findSmallest [] = None"
| "findSmallest (x # xs) =
    (case findSmallest xs of
       None \<Rightarrow> Some x
     | Some m \<Rightarrow> Some (min x m))"

definition findSmallest_postcond ::
    "nat list \<Rightarrow> nat option \<Rightarrow> bool" where
  "findSmallest_postcond s result \<longleftrightarrow>
    (case result of
       None \<Rightarrow> s = []
     | Some r \<Rightarrow>
         r \<in> set s \<and> (\<forall>x\<in>set s. r \<le> x))"

theorem findSmallest_spec_satisfied:
  assumes "findSmallest_precond s"
  shows "findSmallest_postcond s (findSmallest s)"
  sorry

end
