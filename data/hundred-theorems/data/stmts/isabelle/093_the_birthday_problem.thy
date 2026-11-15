(*
  Statement-only formalization of "The Birthday Problem" from Hundred Theorems item 093.
  It states the sharp half-cardinality collision thresholds for assignments of 23 and 22
  people to 365 possible birthdays. This file contains no proof.
*)

theory Birthday_Problem
  imports Main
begin

definition birthday_functions :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set" where
  "birthday_functions people days =
    {f. (\<forall>i<people. f i < days) \<and> (\<forall>i. people \<le> i \<longrightarrow> f i = 0)}"

definition birthday_collisions :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set" where
  "birthday_collisions people days =
    {f \<in> birthday_functions people days. \<not> inj_on f {..<people}}"

theorem birthday_problem:
  "2 * card (birthday_collisions 23 365) > card (birthday_functions 23 365)
    \<and> 2 * card (birthday_collisions 22 365) < card (birthday_functions 22 365)"
  sorry

end
