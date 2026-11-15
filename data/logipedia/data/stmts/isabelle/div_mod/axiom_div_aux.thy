(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_div_aux, catalog title "div_mod.axiom_div_aux": for every
  natural index, the abstract auxiliary division function equals the indexed
  division body as a curried function on natural numbers. This file contains
  no proof.
*)

theory axiom_div_aux
  imports Main
begin

definition filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "filter_nat_type f p = f p"

consts
  div_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  div_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_div_aux:
  "\<forall>p :: nat.
    (div_aux p :: nat \<Rightarrow> nat \<Rightarrow> nat)
      = filter_nat_type div_aux_body p"
  sorry

end
