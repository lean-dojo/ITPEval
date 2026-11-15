(*
  Statement-only formalization of Logipedia corpus artifact
  fact.axiom_fact_body_O, catalog title "fact.axiom_fact_body_O": the
  abstract factorial body at zero is related by the source equality predicate
  to the successor of zero. This file contains no proof.
*)

theory axiom_fact_body_O
  imports Main
begin

consts
  logipedia_connectives_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fact_body :: "nat \<Rightarrow> nat"

theorem axiom_fact_body_O:
  "logipedia_connectives_equal (fact_body 0) (Suc 0)"
  sorry

end
