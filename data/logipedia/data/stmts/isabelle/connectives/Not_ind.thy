(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.Not_ind, catalog title connectives.Not_ind: the primitive
  negation eliminator sends a continuation from A-implies-False to Q and a
  primitive Not A assumption to Q. This file contains no proof.
*)

theory Not_ind
  imports Main
begin

consts
  logipedia_connectives_False :: bool
  logipedia_connectives_Not :: "bool \<Rightarrow> bool"

theorem connectives_Not_ind:
  "\<forall>A Q :: bool.
    ((A \<longrightarrow> logipedia_connectives_False) \<longrightarrow> Q) \<longrightarrow>
    logipedia_connectives_Not A \<longrightarrow> Q"
  sorry

end
