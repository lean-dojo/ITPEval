(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_mod_aux, catalog title "div_mod.axiom_mod_aux": for every
  natural index, the abstract auxiliary remainder function equals the indexed
  remainder body as a curried function on natural numbers. This file contains
  no proof.
*)

theory axiom_mod_aux
  imports Main
begin

definition filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "filter_nat_type f p = f p"

consts
  mod_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  mod_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_mod_aux:
  "\<forall>p :: nat.
    (mod_aux p :: nat \<Rightarrow> nat \<Rightarrow> nat)
      = filter_nat_type mod_aux_body p"
  sorry

end
