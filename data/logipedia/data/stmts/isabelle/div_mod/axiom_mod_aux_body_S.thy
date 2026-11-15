(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_mod_aux_body_S, catalog title
  "div_mod.axiom_mod_aux_body_S": at a successor index, the abstract auxiliary
  remainder body returns the dividend when it is at most the divisor, and
  otherwise recursively computes the remainder. This file contains no proof.
*)

theory axiom_mod_aux_body_S
  imports Main
begin

consts
  mod_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  mod_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_mod_aux_body_S:
  "\<forall>p :: nat.
    (mod_aux_body (Suc p) :: nat \<Rightarrow> nat \<Rightarrow> nat)
      = (\<lambda>m n.
          if m \<le> n
          then m
          else mod_aux p (m - Suc n) n)"
  sorry

end
