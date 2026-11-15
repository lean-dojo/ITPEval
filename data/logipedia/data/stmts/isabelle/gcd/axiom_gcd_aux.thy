(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.axiom_gcd_aux, catalog title "gcd.axiom_gcd_aux": for every natural
  index, the source equality predicate relates the abstract auxiliary gcd
  function to the corresponding indexed gcd body as a curried function on
  natural numbers. This file contains no proof.
*)

theory axiom_gcd_aux
  imports Main
begin

definition filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "filter_nat_type f p = f p"

consts
  logipedia_connectives_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  gcd_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  gcd_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_gcd_aux:
  "\<forall>p :: nat.
    logipedia_connectives_equal
      (gcd_aux p :: nat \<Rightarrow> nat \<Rightarrow> nat)
      (filter_nat_type gcd_aux_body p)"
  sorry

end
