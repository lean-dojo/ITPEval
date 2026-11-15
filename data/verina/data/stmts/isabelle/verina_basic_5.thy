(*
  Statement-only formalization of VERINA corpus artifact verina_basic_5
  (verina__isabelle__verina_basic_5), catalog title "multiply": an executable
  integer program returns the product of its two inputs, together with its
  unconditional precondition, exact integer postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_5
  imports Main
begin

definition multiply_precond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "multiply_precond a b \<longleftrightarrow> True"

definition multiply :: "int \<Rightarrow> int \<Rightarrow> int" where
  "multiply a b = a * b"

definition multiply_postcond :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "multiply_postcond a b result \<longleftrightarrow>
    result - a * b = 0 \<and> a * b - result = 0"

theorem multiply_spec_satisfied:
  assumes "multiply_precond a b"
  shows "multiply_postcond a b (multiply a b)"
  sorry

end
