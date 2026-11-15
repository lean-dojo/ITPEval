(*
  Statement-only formalization of VERINA corpus artifact verina_basic_98
  (verina__isabelle__verina_basic_98), catalog title "Triple": an executable
  integer program returns its input multiplied by three, together with its
  unconditional precondition, integer-division postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_98
  imports Main
begin

definition Triple_precond :: "int \<Rightarrow> bool" where
  "Triple_precond x \<longleftrightarrow> True"

definition Triple :: "int \<Rightarrow> int" where
  "Triple x = x * 3"

definition Triple_postcond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "Triple_postcond x result \<longleftrightarrow>
    result div 3 = x \<and> result div 3 * 3 = result"

theorem Triple_spec_satisfied:
  assumes "Triple_precond x"
  shows "Triple_postcond x (Triple x)"
  sorry

end
