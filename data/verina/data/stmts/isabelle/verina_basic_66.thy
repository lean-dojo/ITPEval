(*
  Statement-only formalization of VERINA corpus artifact verina_basic_66
  (verina__isabelle__verina_basic_66), catalog title "ComputeIsEven": an
  executable integer program tests whether its input has remainder zero
  modulo two, together with its unconditional precondition, integer-witness
  evenness postcondition, and final correctness proposition. This file
  contains no proof.
*)

theory verina_basic_66
  imports Main
begin

definition ComputeIsEven_precond :: "int \<Rightarrow> bool" where
  "ComputeIsEven_precond x \<longleftrightarrow> True"

definition ComputeIsEven :: "int \<Rightarrow> bool" where
  "ComputeIsEven x =
    (if x mod 2 = 0 then True else False)"

definition ComputeIsEven_postcond ::
    "int \<Rightarrow> bool \<Rightarrow> bool" where
  "ComputeIsEven_postcond x result \<longleftrightarrow>
    (result = True \<longleftrightarrow> (\<exists>k :: int. x = 2 * k))"

theorem ComputeIsEven_spec_satisfied:
  assumes "ComputeIsEven_precond x"
  shows "ComputeIsEven_postcond x (ComputeIsEven x)"
  sorry

end
