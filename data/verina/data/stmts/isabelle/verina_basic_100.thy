(*
  Statement-only formalization of VERINA corpus artifact verina_basic_100,
  catalog title "Triple": an executable integer program returns three times
  its input, including the explicit zero branch, together with its trivial
  precondition and integer-division correctness contract. This file contains
  no proof.
*)

theory verina_basic_100
  imports Main
begin

definition Triple_precond :: "int \<Rightarrow> bool" where
  "Triple_precond x \<longleftrightarrow> True"

definition Triple :: "int \<Rightarrow> int" where
  "Triple x =
    (if x = 0 then 0
     else
       (let y = 2 * x
        in x + y))"

definition Triple_postcond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "Triple_postcond x result \<longleftrightarrow>
    result div 3 = x \<and> result div 3 * 3 = result"

theorem Triple_spec_satisfied:
  assumes "Triple_precond x"
  shows "Triple_postcond x (Triple x)"
  sorry

end
