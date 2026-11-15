(*
  Statement-only formalization of Logipedia corpus artifact exp.axiom_exp,
  catalog title "exp.axiom_exp": for all natural bases and exponents, the
  abstract exponentiation function is related by the source equality predicate
  to the corresponding indexed exponentiation body. This file contains no
  proof.
*)

theory axiom_exp
  imports Main
begin

definition filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "filter_nat_type f m = f m"

consts
  logipedia_connectives_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  exp :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  exp_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_exp:
  "\<forall>n m :: nat.
    logipedia_connectives_equal
      (exp n m)
      (filter_nat_type (exp_body n) m)"
  sorry

end
