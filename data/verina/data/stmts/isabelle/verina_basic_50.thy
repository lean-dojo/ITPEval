(*
  Statement-only formalization of VERINA corpus artifact verina_basic_50
  (verina__isabelle__verina_basic_50), catalog title "Abs": an executable
  integer program returns its input when nonnegative and its negation when
  negative, together with its unconditional precondition, absolute-value
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_50
  imports Main
begin

definition Abs_precond :: "int \<Rightarrow> bool" where
  "Abs_precond x \<longleftrightarrow> True"

definition Abs :: "int \<Rightarrow> int" where
  "Abs x = (if x < 0 then -x else x)"

definition Abs_postcond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "Abs_postcond x result \<longleftrightarrow>
    ((x \<ge> 0 \<longrightarrow> x = result) \<and>
     (x < 0 \<longrightarrow> x + result = 0))"

theorem Abs_spec_satisfied:
  assumes "Abs_precond x"
  shows "Abs_postcond x (Abs x)"
  sorry

end
