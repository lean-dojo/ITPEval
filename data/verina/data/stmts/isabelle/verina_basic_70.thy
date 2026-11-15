(*
  Statement-only formalization of VERINA corpus artifact verina_basic_70
  (verina__isabelle__verina_basic_70), catalog title "LinearSearch3": an
  executable left-to-right search of an integer array known to contain an
  element satisfying a Boolean predicate returns the first satisfying index,
  together with the existence precondition, first-occurrence postcondition,
  and final correctness proposition. This file contains no proof.
*)

theory verina_basic_70
  imports Main
begin

definition LinearSearch3_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "LinearSearch3_getBang a i =
    (if i < length a then a ! i else 0)"

definition LinearSearch3_precond ::
    "int list \<Rightarrow> (int \<Rightarrow> bool) \<Rightarrow> bool" where
  "LinearSearch3_precond a P \<longleftrightarrow>
    (\<exists>i. i < length a \<and> P (LinearSearch3_getBang a i))"

fun LinearSearch3_scan ::
    "int list \<Rightarrow> (int \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
  "LinearSearch3_scan [] P n = 0"
| "LinearSearch3_scan (x # xs) P n =
    (if P x
     then n
     else LinearSearch3_scan xs P (Suc n))"

definition LinearSearch3 ::
    "int list \<Rightarrow> (int \<Rightarrow> bool) \<Rightarrow> nat" where
  "LinearSearch3 a P = LinearSearch3_scan a P 0"

definition LinearSearch3_postcond ::
    "int list \<Rightarrow> (int \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "LinearSearch3_postcond a P result \<longleftrightarrow>
    result < length a \<and>
    P (LinearSearch3_getBang a result) \<and>
    (\<forall>k. k < result \<longrightarrow>
      \<not> P (LinearSearch3_getBang a k))"

theorem LinearSearch3_spec_satisfied:
  fixes a :: "int list"
    and P :: "int \<Rightarrow> bool"
  assumes "LinearSearch3_precond a P"
  shows "LinearSearch3_postcond a P (LinearSearch3 a P)"
  sorry

end
