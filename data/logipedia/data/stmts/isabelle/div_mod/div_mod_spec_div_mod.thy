(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.div_mod_spec_div_mod, catalog title div_mod.div_mod_spec_div_mod:
  natural-number quotient and remainder satisfy the Euclidean division
  specification for every positive divisor. This file contains no proof.
*)

theory div_mod_spec_div_mod
  imports Main
begin

definition div_mod_spec :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "div_mod_spec n m q r \<longleftrightarrow> r < m \<and> n = q * m + r"

theorem div_mod_spec_div_mod:
  fixes n m :: nat
  assumes "0 < m"
  shows "div_mod_spec n m (n div m) (n mod m)"
  sorry

end
