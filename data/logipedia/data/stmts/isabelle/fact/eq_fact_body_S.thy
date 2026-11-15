(*
  Statement-only formalization of Logipedia corpus artifact
  fact.eq_fact_body_S, catalog title "fact.eq_fact_body_S": for every natural
  number, the abstract factorial body at its successor is Leibniz-equal to
  the abstract factorial value times that successor. This file contains no
  proof.
*)

theory eq_fact_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  fact :: "nat \<Rightarrow> nat"
  fact_body :: "nat \<Rightarrow> nat"

theorem eq_fact_body_S:
  "\<forall>n :: nat.
    logipedia_leibniz
      (fact_body (Suc n))
      (fact n * Suc n)"
  sorry

end
