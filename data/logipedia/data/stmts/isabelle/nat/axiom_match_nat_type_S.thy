(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_match_nat_type_S, catalog title "nat.axiom_match_nat_type_S":
  for every result type, zero branch, successor branch, and natural number,
  the source equality predicate relates the natural-number matcher at the
  successor to the successor branch applied to that number. This file
  contains no proof.
*)

theory axiom_match_nat_type_S
  imports Main
begin

consts
  logipedia_connectives_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  match_nat_type :: "'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"

theorem axiom_match_nat_type_S:
  "\<forall>case_O :: 'a. \<forall>case_S :: nat \<Rightarrow> 'a. \<forall>n :: nat.
    logipedia_connectives_equal
      (match_nat_type case_O case_S (Suc n))
      (case_S n)"
  sorry

end
