(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_match_nat_type_O, catalog title "nat.axiom_match_nat_type_O":
  for every result type, zero branch, and successor branch, the source
  equality predicate relates the natural-number matcher at zero to the zero
  branch. This file contains no proof.
*)

theory axiom_match_nat_type_O
  imports Main
begin

consts
  logipedia_connectives_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  match_nat_type :: "'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"

theorem axiom_match_nat_type_O:
  "\<forall>case_O :: 'a. \<forall>case_S :: nat \<Rightarrow> 'a.
    logipedia_connectives_equal
      (match_nat_type case_O case_S 0)
      case_O"
  sorry

end
