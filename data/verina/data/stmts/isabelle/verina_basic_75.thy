(*
  Statement-only formalization of VERINA corpus artifact verina_basic_75
  (verina__isabelle__verina_basic_75), catalog title "minArray": an
  executable left-to-right scan of a nonempty integer array returns an array
  element that is less than or equal to every array element, together with its
  precondition, postcondition, and final correctness proposition. This file
  contains no proof.
*)

theory verina_basic_75
  imports Main
begin

definition minArray_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "minArray_getBang a index =
    (if index < length a then a ! index else 0)"

definition minArray_precond :: "int list \<Rightarrow> bool" where
  "minArray_precond a \<longleftrightarrow> length a > 0"

definition minArray_step :: "int \<Rightarrow> int \<Rightarrow> int" where
  "minArray_step current candidate =
    (if current > candidate then candidate else current)"

definition minArray_loop ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "minArray_loop a index current =
    foldl minArray_step current (drop index a)"

definition minArray :: "int list \<Rightarrow> int" where
  "minArray a =
    minArray_loop a 1 (minArray_getBang a 0)"

definition minArray_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "minArray_postcond a result \<longleftrightarrow>
    (\<forall>i<length a. result \<le> minArray_getBang a i) \<and>
    (\<exists>i<length a. result = minArray_getBang a i)"

theorem minArray_spec_satisfied:
  fixes a :: "int list"
  assumes "minArray_precond a"
  shows "minArray_postcond a (minArray a)"
  sorry

end
