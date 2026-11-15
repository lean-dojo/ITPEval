(*
  Statement-only formalization of VERINA corpus artifact verina_basic_101,
  catalog title "Triple": an executable integer program computes twice its
  input in a local variable and adds the input once more, together with its
  trivial precondition and integer-division correctness contract. This file
  contains no proof.
*)

theory verina_basic_101
  imports Main
begin

definition Triple_precond :: "int \<Rightarrow> bool" where
  "Triple_precond x \<longleftrightarrow> True"

definition Triple :: "int \<Rightarrow> int" where
  "Triple x =
    (let y = x * 2
     in y + x)"

definition Triple_postcond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "Triple_postcond x result \<longleftrightarrow>
    result div 3 = x \<and> result div 3 * 3 = result"

theorem Triple_spec_satisfied:
  assumes "Triple_precond x"
  shows "Triple_postcond x (Triple x)"
  sorry

end
