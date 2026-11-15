(*
  Statement-only formalization of Logipedia corpus artifact logic.absurd,
  catalog title "logic.absurd": a proposition together with its primitive
  negation entails the module's primitive falsity proposition. This file
  contains no proof.
*)

theory absurd
  imports Main
begin

consts
  logipedia_connectives_False :: bool
  logipedia_connectives_Not :: "bool \<Rightarrow> bool"

theorem logic_absurd:
  "\<forall>A :: bool.
    A \<longrightarrow>
    logipedia_connectives_Not A \<longrightarrow>
    logipedia_connectives_False"
  sorry

end
