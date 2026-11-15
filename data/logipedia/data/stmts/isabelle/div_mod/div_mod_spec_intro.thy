(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.div_mod_spec_intro, catalog title "div_mod.div_mod_spec_intro":
  a remainder bound and quotient-remainder decomposition introduce the
  natural-number Euclidean division specification. This file contains no
  proof.
*)

theory div_mod_spec_intro
  imports Main
begin

definition div_mod_spec :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "div_mod_spec n m q r \<longleftrightarrow> r < m \<and> n = q * m + r"

theorem div_mod_spec_intro:
  fixes n m q r :: nat
  assumes "r < m"
    and "n = q * m + r"
  shows "div_mod_spec n m q r"
  sorry

end
