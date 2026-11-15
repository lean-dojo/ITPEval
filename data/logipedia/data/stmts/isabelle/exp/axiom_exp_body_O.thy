(*
  Statement-only formalization of Logipedia corpus artifact
  exp.axiom_exp_body_O, catalog title "exp.axiom_exp_body_O": for every
  natural base, the abstract exponentiation body at exponent zero equals
  the successor of zero. This file contains no proof.
*)

theory axiom_exp_body_O
  imports Main
begin

consts
  exp_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_exp_body_O:
  "\<forall>n :: nat. exp_body n 0 = Suc 0"
  sorry

end
