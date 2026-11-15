(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.ex_intro, catalog title "connectives.ex_intro": existential
  introduction for the module's primitive existential connective from a
  predicate and an internal witness satisfying it. This file contains no proof.
*)

theory ex_intro
  imports Main
begin

consts logipedia_connectives_ex :: "('a \<Rightarrow> bool) \<Rightarrow> bool"

theorem connectives_ex_intro:
  "\<forall>P :: 'a \<Rightarrow> bool. \<forall>x :: 'a.
    P x \<longrightarrow> logipedia_connectives_ex P"
  sorry

end
