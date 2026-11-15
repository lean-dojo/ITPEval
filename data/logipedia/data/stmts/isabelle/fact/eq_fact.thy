(*
  Statement-only formalization of Logipedia corpus artifact fact.eq_fact,
  catalog title "fact.eq_fact": for every natural number, the abstract
  factorial function is Leibniz-equal to the corresponding indexed factorial
  body. This file contains no proof.
*)

theory eq_fact
  imports Main
begin

definition filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "filter_nat_type f n = f n"

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  fact :: "nat \<Rightarrow> nat"
  fact_body :: "nat \<Rightarrow> nat"

theorem eq_fact:
  "\<forall>n :: nat.
    logipedia_leibniz
      (fact n)
      (filter_nat_type fact_body n)"
  sorry

end
