(*
  Statement-only formalization of Logipedia corpus artifact logic.not_to_not,
  catalog title "logic.not_to_not": contraposition for the module's primitive
  negation connective, represented by Isabelle negation: an implication from
  A to B and negation of B entail negation of A. This file contains no proof.
*)

theory not_to_not
  imports Main
begin

definition logipedia_connectives_Not :: "bool \<Rightarrow> bool"
  where "logipedia_connectives_Not P \<longleftrightarrow> \<not> P"

theorem logic_not_to_not:
  "\<forall>A B :: bool.
    (A \<longrightarrow> B) \<longrightarrow>
    logipedia_connectives_Not B \<longrightarrow>
    logipedia_connectives_Not A"
  sorry

end
