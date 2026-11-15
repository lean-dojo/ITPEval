(*
  Statement-only formalization of VERINA corpus artifact verina_basic_80
  (verina__isabelle__verina_basic_80), catalog title "only_once": an
  executable left-to-right scan counts occurrences of an integer key in an
  array and returns true exactly when the count is one, together with its
  unconditional precondition, postcondition, and final correctness
  proposition. This file contains no proof.
*)

theory verina_basic_80
  imports Main
begin

definition only_once_precond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "only_once_precond a key \<longleftrightarrow> True"

fun only_once_scan ::
    "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "only_once_scan [] key keyCount = (keyCount = 1)"
| "only_once_scan (val # rest) key keyCount =
    only_once_scan rest key
      (if val = key then keyCount + 1 else keyCount)"

definition only_once_loop ::
    "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "only_once_loop a key i keyCount =
    only_once_scan (drop i a) key keyCount"

definition only_once :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "only_once a key = only_once_loop a key 0 0"

definition count_occurrences ::
    "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count_occurrences a key =
    foldl
      (\<lambda>cnt x. if x = key then cnt + 1 else cnt)
      0 a"

definition only_once_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> bool" where
  "only_once_postcond a key result \<longleftrightarrow>
    (count_occurrences a key = 1 \<longrightarrow> result) \<and>
    (count_occurrences a key \<noteq> 1 \<longrightarrow> \<not> result)"

theorem only_once_spec_satisfied:
  fixes a :: "int list"
    and key :: int
  assumes "only_once_precond a key"
  shows "only_once_postcond a key (only_once a key)"
  sorry

end
