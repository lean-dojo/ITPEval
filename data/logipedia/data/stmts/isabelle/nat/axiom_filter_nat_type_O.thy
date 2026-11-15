(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_filter_nat_type_O, catalog title "nat.axiom_filter_nat_type_O":
  for every result type and natural-number-indexed return function, the source
  equality predicate relates filtering that function at zero to its value at
  zero. This file contains no proof.
*)

theory axiom_filter_nat_type_O
  imports Main
begin

consts
  logipedia_connectives_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"

theorem axiom_filter_nat_type_O:
  "\<forall>ret :: nat \<Rightarrow> 'a.
    logipedia_connectives_equal
      (filter_nat_type ret 0)
      (ret 0)"
  sorry

end
