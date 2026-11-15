(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.match_ex_prop, catalog title "connectives.match_ex_prop":
  elimination for the module's primitive existential connective over a
  possibly empty carrier, deriving a result from a continuation valid for
  every carrier witness satisfying the predicate. This file contains no proof.
*)

theory match_ex_prop
  imports Main
begin

consts logipedia_connectives_ex :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"

theorem connectives_match_ex_prop:
  "\<forall>A P :: 'a set. \<forall>return :: bool.
    P \<subseteq> A \<longrightarrow>
    (\<forall>x \<in> A. x \<in> P \<longrightarrow> return) \<longrightarrow>
    logipedia_connectives_ex A P \<longrightarrow> return"
  sorry

end
