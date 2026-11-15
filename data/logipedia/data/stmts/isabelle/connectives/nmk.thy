(*
  Statement-only formalization of Logipedia corpus artifact connectives.nmk,
  catalog title "connectives.nmk": introduction for the module's primitive
  negation connective from an implication of the proposition to the module's
  primitive falsity proposition. This file contains no proof.
*)

theory nmk
  imports Main
begin

consts
  logipedia_connectives_False :: bool
  logipedia_connectives_Not :: "bool \<Rightarrow> bool"

theorem connectives_nmk:
  "\<forall>A :: bool.
    (A \<longrightarrow> logipedia_connectives_False) \<longrightarrow>
    logipedia_connectives_Not A"
  sorry

end
