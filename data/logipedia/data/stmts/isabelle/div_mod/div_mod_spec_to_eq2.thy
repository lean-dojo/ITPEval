(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.div_mod_spec_to_eq2, catalog title "div_mod.div_mod_spec_to_eq2":
  two natural-number quotient-remainder decompositions of the same dividend
  with remainders below the same divisor have equal remainders. This file
  contains no proof.
*)

theory div_mod_spec_to_eq2
  imports Main
begin

definition div_mod_spec :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "div_mod_spec n m q r \<longleftrightarrow> r < m \<and> n = q * m + r"

theorem div_mod_spec_to_eq2:
  fixes a b q r q1 r1 :: nat
  assumes "div_mod_spec a b q r"
    and "div_mod_spec a b q1 r1"
  shows "r = r1"
  sorry

end
