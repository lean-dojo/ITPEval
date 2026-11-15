(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.match_div_mod_spec_prop, catalog title
  "div_mod.match_div_mod_spec_prop": elimination of the natural-number
  quotient-remainder specification into an arbitrary proposition from its
  remainder bound and decomposition equation. This file contains no proof.
*)

theory match_div_mod_spec_prop
  imports Main
begin

definition div_mod_spec :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "div_mod_spec n m q r \<longleftrightarrow> r < m \<and> n = q * m + r"

theorem match_div_mod_spec_prop:
  "\<forall>(n :: nat) m q r. \<forall>return :: bool.
    ((r < m \<longrightarrow> n = q * m + r \<longrightarrow> return) \<longrightarrow>
      div_mod_spec n m q r \<longrightarrow> return)"
  sorry

end
