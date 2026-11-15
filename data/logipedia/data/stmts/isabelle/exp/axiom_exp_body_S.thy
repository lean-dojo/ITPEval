(*
  Statement-only formalization of Logipedia corpus artifact
  exp.axiom_exp_body_S, catalog title "exp.axiom_exp_body_S": for every
  natural base and exponent, the abstract exponentiation body at the successor
  exponent equals the preceding abstract exponentiation value times the base.
  This file contains no proof.
*)

theory axiom_exp_body_S
  imports Main
begin

consts
  exp :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  exp_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_exp_body_S:
  "\<forall>n m :: nat. exp_body n (Suc m) = exp n m * n"
  sorry

end
