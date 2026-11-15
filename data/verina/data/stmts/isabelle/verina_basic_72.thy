(*
  Statement-only formalization of VERINA corpus artifact verina_basic_72
  (verina__isabelle__verina_basic_72), catalog title "append": an executable
  integer-array program copies an input array and appends one integer,
  together with its unconditional precondition, elementwise-and-length
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_72
  imports Main
begin

definition append_precond :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "append_precond a b \<longleftrightarrow> True"

fun append_copy_loop ::
    "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "append_copy_loop [] acc = acc"
| "append_copy_loop (x # xs) acc =
    append_copy_loop xs (acc @ [x])"

definition copy ::
    "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list" where
  "copy a i acc = append_copy_loop (drop i a) acc"

definition append_program :: "int list \<Rightarrow> int \<Rightarrow> int list" where
  "append_program a b =
    (let c_initial = copy a 0 [];
         c_full = c_initial @ [b]
     in c_full)"

definition append_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "append_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition append_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> bool" where
  "append_postcond a b result \<longleftrightarrow>
    (\<forall>i<length a.
      append_getBang result i = append_getBang a i) \<and>
    append_getBang result (length a) = b \<and>
    length result = length a + 1"

theorem append_spec_satisfied:
  fixes a :: "int list"
    and b :: int
  assumes "append_precond a b"
  shows "append_postcond a b (append_program a b)"
  sorry

end
