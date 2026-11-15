(*
  Statement-only formalization of VERINA corpus artifact verina_basic_94
  (verina__isabelle__verina_basic_94), catalog title "iter_copy": an
  executable left-to-right integer-array copy, together with its
  unconditional precondition, elementwise-and-length postcondition, and
  final correctness proposition. This file contains no proof.
*)

theory verina_basic_94
  imports Main
begin

definition iter_copy_precond :: "int list \<Rightarrow> bool" where
  "iter_copy_precond s \<longleftrightarrow> True"

fun iter_copy_remaining ::
    "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "iter_copy_remaining [] acc = acc"
| "iter_copy_remaining (x # xs) acc =
    iter_copy_remaining xs (acc @ [x])"

definition iter_copy_loop ::
    "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list" where
  "iter_copy_loop s i acc =
    iter_copy_remaining (drop i s) acc"

definition iter_copy :: "int list \<Rightarrow> int list" where
  "iter_copy s = iter_copy_loop s 0 []"

definition iter_copy_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "iter_copy_postcond s result \<longleftrightarrow>
    length s = length result \<and>
    (\<forall>i. i < length s \<longrightarrow> s ! i = result ! i)"

theorem iter_copy_spec_satisfied:
  fixes s :: "int list"
  assumes "iter_copy_precond s"
  shows "iter_copy_postcond s (iter_copy s)"
  sorry

end
