(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_mod_aux_body_O, catalog title
  "div_mod.axiom_mod_aux_body_O": at index zero, the abstract auxiliary
  remainder body is the first-projection curried function on natural numbers.
  This file contains no proof.
*)

theory axiom_mod_aux_body_O
  imports Main
begin

consts
  mod_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_mod_aux_body_O:
  "(mod_aux_body 0 :: nat \<Rightarrow> nat \<Rightarrow> nat)
    = (\<lambda>m n. m)"
  sorry

end
