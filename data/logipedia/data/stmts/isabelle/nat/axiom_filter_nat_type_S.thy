(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_filter_nat_type_S, catalog title "nat.axiom_filter_nat_type_S":
  for every result type, natural-number-indexed return function, and natural
  number, the source equality predicate relates filtering that function at
  the successor to its value at the successor. This file contains no proof.
*)

theory axiom_filter_nat_type_S
  imports Main
begin

consts
  logipedia_connectives_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"

theorem axiom_filter_nat_type_S:
  "\<forall>ret :: nat \<Rightarrow> 'a. \<forall>n :: nat.
    logipedia_connectives_equal
      (filter_nat_type ret (Suc n))
      (ret (Suc n))"
  sorry

end
