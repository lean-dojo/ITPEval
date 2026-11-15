(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_div_aux_body_O, catalog title
  "div_mod.axiom_div_aux_body_O": at index zero, the abstract auxiliary
  division body is the constant-zero curried function on natural numbers.
  This file contains no proof.
*)

theory axiom_div_aux_body_O
  imports Main
begin

consts
  div_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_div_aux_body_O:
  "(div_aux_body 0 :: nat \<Rightarrow> nat \<Rightarrow> nat)
    = (\<lambda>m n. 0)"
  sorry

end
