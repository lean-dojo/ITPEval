(*
  Statement-only formalization of Logipedia corpus artifact
  fact.axiom_fact_body_S, catalog title "fact.axiom_fact_body_S": for every
  natural number, the abstract factorial body at its successor equals the
  abstract factorial value times that successor. This file contains no proof.
*)

theory axiom_fact_body_S
  imports Main
begin

consts
  fact :: "nat \<Rightarrow> nat"
  fact_body :: "nat \<Rightarrow> nat"

theorem axiom_fact_body_S:
  "\<forall>n :: nat. fact_body (Suc n) = fact n * Suc n"
  sorry

end
