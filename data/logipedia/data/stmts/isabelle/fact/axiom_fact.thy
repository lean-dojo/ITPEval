(*
  Statement-only formalization of Logipedia corpus artifact fact.axiom_fact,
  catalog title "fact.axiom_fact": for every natural number, the abstract
  factorial function is related by the source equality predicate to the
  corresponding indexed factorial body. This file contains no proof.
*)

theory axiom_fact
  imports Main
begin

definition filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "filter_nat_type f n = f n"

consts
  logipedia_connectives_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fact :: "nat \<Rightarrow> nat"
  fact_body :: "nat \<Rightarrow> nat"

theorem axiom_fact:
  "\<forall>n :: nat.
    logipedia_connectives_equal
      (fact n)
      (filter_nat_type fact_body n)"
  sorry

end
