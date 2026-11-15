(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_div_aux_body_S, catalog title
  "div_mod.axiom_div_aux_body_S": at a successor index, the abstract auxiliary
  division body returns zero when the dividend is at most the divisor, and
  otherwise recursively computes the successor quotient. This file contains
  no proof.
*)

theory axiom_div_aux_body_S
  imports Main
begin

consts
  div_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  div_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_div_aux_body_S:
  "\<forall>p :: nat.
    (div_aux_body (Suc p) :: nat \<Rightarrow> nat \<Rightarrow> nat)
      = (\<lambda>m n.
          if m \<le> n
          then 0
          else Suc (div_aux p (m - Suc n) n))"
  sorry

end
