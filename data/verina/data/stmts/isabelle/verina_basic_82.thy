(*
  Statement-only formalization of VERINA corpus artifact verina_basic_82
  (verina__isabelle__verina_basic_82), catalog title "remove_front": an
  executable integer-array program copies the suffix beginning at index one,
  thereby removing the first element of a nonempty array, together with its
  precondition, elementwise-and-length postcondition, and final correctness
  proposition. This file contains no proof.
*)

theory verina_basic_82
  imports Main
begin

definition remove_front_precond :: "int list \<Rightarrow> bool" where
  "remove_front_precond a \<longleftrightarrow> length a > 0"

fun copyFrom_loop ::
    "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "copyFrom_loop [] acc = acc"
| "copyFrom_loop (x # xs) acc =
    copyFrom_loop xs (acc @ [x])"

definition copyFrom ::
    "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list" where
  "copyFrom a i acc = copyFrom_loop (drop i a) acc"

definition remove_front :: "int list \<Rightarrow> int list" where
  "remove_front a =
    (if length a > 0
     then
       (let c = copyFrom a 1 []
        in c)
     else [])"

definition remove_front_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "remove_front_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition remove_front_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "remove_front_postcond a result \<longleftrightarrow>
    length a > 0 \<and>
    length result = length a - 1 \<and>
    (\<forall>i. i < length result \<longrightarrow>
      remove_front_getBang result i =
        remove_front_getBang a (i + 1))"

theorem remove_front_spec_satisfied:
  fixes a :: "int list"
  assumes "remove_front_precond a"
  shows "remove_front_postcond a (remove_front a)"
  sorry

end
