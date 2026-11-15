(*
  Statement-only formalization of VERINA corpus artifact verina_basic_19,
  catalog title "isSorted": an executable integer-array program returns true
  exactly when every adjacent pair is in non-decreasing order, together with
  its trivial precondition, Boolean postcondition, and correctness contract.
  This file contains no proof.
*)

theory verina_basic_19
  imports Main
begin

definition isSorted_precond :: "int list \<Rightarrow> bool" where
  "isSorted_precond a \<longleftrightarrow> True"

definition isSorted_mapIdx :: "int list \<Rightarrow> bool list" where
  "isSorted_mapIdx a =
    map
      (\<lambda>(i, x).
        if i + 1 < length a
        then x \<le> a ! (i + 1)
        else True)
      (zip [0..<length a] a)"

definition isSorted :: "int list \<Rightarrow> bool" where
  "isSorted a =
    (if length a \<le> 1
     then True
     else list_all id (isSorted_mapIdx a))"

definition isSorted_postcond ::
    "int list \<Rightarrow> bool \<Rightarrow> bool" where
  "isSorted_postcond a result \<longleftrightarrow>
    ((\<forall>i<length a - 1. a ! i \<le> a ! (i + 1)) \<longleftrightarrow> result)"

theorem isSorted_spec_satisfied:
  assumes "isSorted_precond a"
  shows "isSorted_postcond a (isSorted a)"
  sorry

end
