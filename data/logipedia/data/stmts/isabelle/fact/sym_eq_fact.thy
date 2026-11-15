(*
  Statement-only formalization of Logipedia corpus artifact fact.sym_eq_fact,
  catalog title "fact.sym_eq_fact": for every natural number, the corresponding
  indexed factorial body is Leibniz-equal to the abstract factorial function.
  This file contains no proof.
*)

theory sym_eq_fact
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

theorem sym_eq_fact:
  "\<forall>n :: nat.
    logipedia_leibniz
      (filter_nat_type fact_body n)
      (fact n)"
  sorry

end
