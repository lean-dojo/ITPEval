(*
  Statement-only formalization of VERINA corpus artifact verina_basic_10,
  catalog title "isGreater": an executable integer-array program returns true
  exactly when the given integer is strictly greater than every array element,
  under the nonempty-array precondition. This file contains no proof.
*)

theory verina_basic_10
  imports Main
begin

definition isGreater_precond :: "int \<Rightarrow> int list \<Rightarrow> bool" where
  "isGreater_precond n a \<longleftrightarrow> length a > 0"

definition isGreater :: "int \<Rightarrow> int list \<Rightarrow> bool" where
  "isGreater n a = list_all (\<lambda>x. n > x) a"

definition isGreater_postcond ::
    "int \<Rightarrow> int list \<Rightarrow> bool \<Rightarrow> bool" where
  "isGreater_postcond n a result \<longleftrightarrow>
    ((\<forall>i<length a. n > a ! i) \<longleftrightarrow> result)"

theorem isGreater_spec_satisfied:
  assumes "isGreater_precond n a"
  shows "isGreater_postcond n a (isGreater n a)"
  sorry

end
