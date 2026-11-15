(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.match_Or_prop, catalog title "connectives.match_Or_prop":
  elimination for the module's primitive binary disjunction connective,
  deriving a result from continuations for either branch. This file contains
  no proof.
*)

theory match_Or_prop
  imports Main
begin

consts logipedia_connectives_Or :: "bool \<Rightarrow> bool \<Rightarrow> bool"

theorem connectives_match_Or_prop:
  "\<forall>A B return :: bool.
    (A \<longrightarrow> return) \<longrightarrow>
    (B \<longrightarrow> return) \<longrightarrow>
    logipedia_connectives_Or A B \<longrightarrow> return"
  sorry

end
