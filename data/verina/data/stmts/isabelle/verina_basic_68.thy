(*
  Statement-only formalization of VERINA corpus artifact verina_basic_68
  (verina__isabelle__verina_basic_68), catalog title "LinearSearch": an
  executable left-to-right search of an integer array returns the first index
  containing the target, or the array length when the target is absent,
  together with its unconditional precondition, first-occurrence
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_68
  imports Main
begin

definition LinearSearch_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "LinearSearch_getBang a i =
    (if i < length a then a ! i else 0)"

definition LinearSearch_precond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "LinearSearch_precond a e \<longleftrightarrow> True"

fun LinearSearch_scan ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat" where
  "LinearSearch_scan [] e n = n"
| "LinearSearch_scan (x # xs) e n =
    (if x = e
     then n
     else LinearSearch_scan xs e (Suc n))"

definition LinearSearch_loop ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat" where
  "LinearSearch_loop a e n =
    LinearSearch_scan (drop n a) e n"

definition LinearSearch ::
    "int list \<Rightarrow> int \<Rightarrow> nat" where
  "LinearSearch a e = LinearSearch_loop a e 0"

definition LinearSearch_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool" where
  "LinearSearch_postcond a e result \<longleftrightarrow>
    result \<le> length a \<and>
    (result = length a \<or> LinearSearch_getBang a result = e) \<and>
    (\<forall>i. i < result \<longrightarrow> LinearSearch_getBang a i \<noteq> e)"

theorem LinearSearch_spec_satisfied:
  assumes "LinearSearch_precond a e"
  shows "LinearSearch_postcond a e (LinearSearch a e)"
  sorry

end
