(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.or_intror, catalog title "connectives.or_intror": right
  introduction for the module's primitive binary disjunction connective.
  This file contains no proof.
*)

theory or_intror
  imports Main
begin

consts logipedia_connectives_Or :: "bool \<Rightarrow> bool \<Rightarrow> bool"

theorem connectives_or_intror:
  "\<forall>A B :: bool.
    B \<longrightarrow> logipedia_connectives_Or A B"
  sorry

end
