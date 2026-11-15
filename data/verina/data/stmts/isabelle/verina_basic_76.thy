(*
  Statement-only formalization of VERINA corpus artifact verina_basic_76
  (verina__isabelle__verina_basic_76), catalog title "myMin": an executable
  comparison program returns the smaller of two integers, together with its
  trivial precondition, conditional postcondition, and final correctness
  proposition. This file contains no proof.
*)

theory verina_basic_76
  imports Main
begin

definition myMin_precond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "myMin_precond x y \<longleftrightarrow> True"

definition myMin :: "int \<Rightarrow> int \<Rightarrow> int" where
  "myMin x y = (if x < y then x else y)"

definition myMin_postcond ::
    "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "myMin_postcond x y result \<longleftrightarrow>
    (x \<le> y \<longrightarrow> result = x) \<and>
    (x > y \<longrightarrow> result = y)"

theorem myMin_spec_satisfied:
  fixes x y :: int
  assumes "myMin_precond x y"
  shows "myMin_postcond x y (myMin x y)"
  sorry

end
