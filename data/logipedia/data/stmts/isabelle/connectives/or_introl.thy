(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.or_introl, catalog title "connectives.or_introl": left
  introduction for the module's primitive binary disjunction connective.
  This file contains no proof.
*)

theory or_introl
  imports Main
begin

consts logipedia_connectives_Or :: "bool \<Rightarrow> bool \<Rightarrow> bool"

theorem connectives_or_introl:
  "\<forall>A B :: bool.
    A \<longrightarrow> logipedia_connectives_Or A B"
  sorry

end
