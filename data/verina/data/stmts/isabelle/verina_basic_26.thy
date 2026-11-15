(*
  Statement-only formalization of VERINA corpus artifact verina_basic_26
  (verina__isabelle__verina_basic_26), catalog title "isEven": an executable
  integer program returns true exactly when its input has remainder zero
  modulo two, together with its unconditional precondition, Boolean
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_26
  imports Main
begin

definition isEven_precond :: "int \<Rightarrow> bool" where
  "isEven_precond n \<longleftrightarrow> True"

definition isEven :: "int \<Rightarrow> bool" where
  "isEven n = (n mod 2 = 0)"

definition isEven_postcond :: "int \<Rightarrow> bool \<Rightarrow> bool" where
  "isEven_postcond n result \<longleftrightarrow>
    ((result \<longrightarrow> n mod 2 = 0) \<and>
     (\<not> result \<longrightarrow> n mod 2 \<noteq> 0))"

theorem isEven_spec_satisfied:
  assumes "isEven_precond n"
  shows "isEven_postcond n (isEven n)"
  sorry

end
