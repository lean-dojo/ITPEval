(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.match_And_prop, catalog title "connectives.match_And_prop":
  elimination for the module's primitive binary conjunction connective,
  applying a continuation that consumes both conjuncts. This file contains
  no proof.
*)

theory match_And_prop
  imports Main
begin

consts logipedia_connectives_And :: "bool \<Rightarrow> bool \<Rightarrow> bool"

theorem connectives_match_And_prop:
  "\<forall>A B return :: bool.
    (A \<longrightarrow> B \<longrightarrow> return) \<longrightarrow>
    logipedia_connectives_And A B \<longrightarrow> return"
  sorry

end
