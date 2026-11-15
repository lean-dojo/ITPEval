(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_40,
  catalog title "maxOfList": an executable recursive program returns the
  maximum element of a nonempty natural-number list, together with its
  membership and upper-bound correctness contract. This file contains no proof.
*)

theory verina_advanced_40
  imports Main
begin

definition maxOfList_precond :: "nat list \<Rightarrow> bool" where
  "maxOfList_precond lst \<longleftrightarrow> lst \<noteq> []"

fun maxOfList_helper :: "nat list \<Rightarrow> nat" where
  "maxOfList_helper [] = 0"
| "maxOfList_helper [x] = x"
| "maxOfList_helper (x # y # xs) =
    (let maxTail = maxOfList_helper (y # xs)
     in if x > maxTail then x else maxTail)"

definition maxOfList :: "nat list \<Rightarrow> nat" where
  "maxOfList lst = maxOfList_helper lst"

definition maxOfList_postcond :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "maxOfList_postcond lst result \<longleftrightarrow>
    result \<in> set lst \<and> (\<forall>x\<in>set lst. x \<le> result)"

theorem maxOfList_spec_satisfied:
  assumes "maxOfList_precond lst"
  shows "maxOfList_postcond lst (maxOfList lst)"
  sorry

end
