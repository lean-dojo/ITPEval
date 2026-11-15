(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.refl_equal, catalog title "connectives.refl_equal": the module's
  polymorphic equality relation is reflexive for every element of every type.
  This file contains no proof.
*)

theory refl_equal
  imports Main
begin

consts logipedia_connectives_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

theorem connectives_refl_equal:
  "\<forall>x :: 'a. logipedia_connectives_equal x x"
  sorry

end
