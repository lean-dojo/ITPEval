(*
  Statement-only formalization of VERINA corpus artifact verina_basic_74
  (verina__isabelle__verina_basic_74), catalog title "maxArray": an
  executable left-to-right scan of a nonempty integer array returns an array
  element that is greater than or equal to every array element, together with
  its precondition, postcondition, and final correctness proposition. This
  file contains no proof.
*)

theory verina_basic_74
  imports Main
begin

definition maxArray_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "maxArray_getBang a index =
    (if index < length a then a ! index else 0)"

definition maxArray_precond :: "int list \<Rightarrow> bool" where
  "maxArray_precond a \<longleftrightarrow> length a > 0"

definition maxArray_step :: "int \<Rightarrow> int \<Rightarrow> int" where
  "maxArray_step current candidate =
    (if current > candidate then current else candidate)"

definition maxArray_aux ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "maxArray_aux a index current =
    foldl maxArray_step current (drop index a)"

definition maxArray :: "int list \<Rightarrow> int" where
  "maxArray a =
    maxArray_aux a 1 (maxArray_getBang a 0)"

definition maxArray_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "maxArray_postcond a result \<longleftrightarrow>
    (\<forall>k<length a. result \<ge> maxArray_getBang a k) \<and>
    (\<exists>k<length a. result = maxArray_getBang a k)"

theorem maxArray_spec_satisfied:
  fixes a :: "int list"
  assumes "maxArray_precond a"
  shows "maxArray_postcond a (maxArray a)"
  sorry

end
