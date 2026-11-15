(*
  Statement-only formalization of VERINA corpus artifact verina_basic_69
  (verina__isabelle__verina_basic_69), catalog title "LinearSearch": an
  executable left-to-right search of an integer array known to contain the
  target returns its first matching index, together with the existence
  precondition, first-occurrence postcondition, and final correctness
  proposition. This file contains no proof.
*)

theory verina_basic_69
  imports Main
begin

definition LinearSearch_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "LinearSearch_getBang a i =
    (if i < length a then a ! i else 0)"

definition LinearSearch_precond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "LinearSearch_precond a e \<longleftrightarrow>
    (\<exists>i. i < length a \<and> LinearSearch_getBang a i = e)"

fun linearSearchAux_scan ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat" where
  "linearSearchAux_scan [] e n = 0"
| "linearSearchAux_scan (x # xs) e n =
    (if x = e
     then n
     else linearSearchAux_scan xs e (Suc n))"

definition linearSearchAux ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat" where
  "linearSearchAux a e n =
    linearSearchAux_scan (drop n a) e n"

definition LinearSearch ::
    "int list \<Rightarrow> int \<Rightarrow> nat" where
  "LinearSearch a e = linearSearchAux a e 0"

definition LinearSearch_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool" where
  "LinearSearch_postcond a e result \<longleftrightarrow>
    result < length a \<and>
    LinearSearch_getBang a result = e \<and>
    (\<forall>k. k < result \<longrightarrow> LinearSearch_getBang a k \<noteq> e)"

theorem LinearSearch_spec_satisfied:
  assumes "LinearSearch_precond a e"
  shows "LinearSearch_postcond a e (LinearSearch a e)"
  sorry

end
