(*
  Statement-only formalization of VERINA corpus artifact verina_basic_107,
  catalog title "ComputeAvg": an executable integer program computes the
  Euclidean quotient of the sum of two integers by two, together with its
  trivial precondition and remainder-based correctness contract. This file
  contains no proof.
*)

theory verina_basic_107
  imports Main
begin

definition ComputeAvg_precond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "ComputeAvg_precond a b \<longleftrightarrow> True"

definition ComputeAvg :: "int \<Rightarrow> int \<Rightarrow> int" where
  "ComputeAvg a b = (a + b) div 2"

definition ComputeAvg_postcond ::
    "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "ComputeAvg_postcond a b result \<longleftrightarrow>
    2 * result = a + b - ((a + b) mod 2)"

theorem ComputeAvg_spec_satisfied:
  assumes "ComputeAvg_precond a b"
  shows "ComputeAvg_postcond a b (ComputeAvg a b)"
  sorry

end
