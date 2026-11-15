(*
  Statement-only formalization of VERINA corpus artifact verina_basic_8
  (verina__isabelle__verina_basic_8), catalog title "myMin": an executable
  comparison program returns the minimum of two integers, together with its
  unconditional precondition, lower-bound and input-membership postcondition,
  and final correctness proposition. This file contains no proof.
*)

theory verina_basic_8
  imports Main
begin

definition myMin_precond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "myMin_precond a b \<longleftrightarrow> True"

definition myMin :: "int \<Rightarrow> int \<Rightarrow> int" where
  "myMin a b = (if a \<le> b then a else b)"

definition myMin_postcond ::
    "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "myMin_postcond a b result \<longleftrightarrow>
    (result \<le> a \<and> result \<le> b) \<and>
    (result = a \<or> result = b)"

theorem myMin_spec_satisfied:
  fixes a b :: int
  assumes "myMin_precond a b"
  shows "myMin_postcond a b (myMin a b)"
  sorry

end
