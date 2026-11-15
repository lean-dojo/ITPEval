(*
  Statement-only formalization of VERINA corpus artifact verina_basic_9
  (verina__isabelle__verina_basic_9), catalog title "hasCommonElement": an
  executable integer-array program returns true exactly when its two nonempty
  input arrays share an element, together with the precondition, Boolean
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_9
  imports Main
begin

definition hasCommonElement_precond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "hasCommonElement_precond a b \<longleftrightarrow>
    length a > 0 \<and> length b > 0"

definition hasCommonElement ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "hasCommonElement a b =
    list_ex (\<lambda>x. list_ex (\<lambda>y. x = y) b) a"

definition hasCommonElement_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool \<Rightarrow> bool" where
  "hasCommonElement_postcond a b result \<longleftrightarrow>
    ((\<exists>i<length a. \<exists>j<length b. a ! i = b ! j)
      \<longleftrightarrow> result)"

theorem hasCommonElement_spec_satisfied:
  assumes "hasCommonElement_precond a b"
  shows "hasCommonElement_postcond a b (hasCommonElement a b)"
  sorry

end
