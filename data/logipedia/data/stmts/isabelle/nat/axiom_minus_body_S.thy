(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_minus_body_S, catalog title "nat.axiom_minus_body_S": at every
  successor, the abstract natural subtraction body is related by the source
  equality predicate to its natural-number case function. This file contains
  no proof.
*)

theory axiom_minus_body_S
  imports Main
begin

consts
  logipedia_connectives_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  match_nat_type :: "'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"
  minus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  minus_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_minus_body_S:
  "\<forall>n :: nat.
    logipedia_connectives_equal
      (minus_body (Suc n))
      (\<lambda>m. match_nat_type (Suc n) (\<lambda>q. minus n q) m)"
  sorry

end
