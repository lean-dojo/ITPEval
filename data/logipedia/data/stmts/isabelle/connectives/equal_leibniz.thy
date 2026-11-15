(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.equal_leibniz, catalog title "connectives.equal_leibniz":
  the module's polymorphic equality relation supports Leibniz substitution
  for every predicate. This file contains no proof.
*)

theory equal_leibniz
  imports Main
begin

consts logipedia_connectives_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

theorem connectives_equal_leibniz:
  "\<forall>x y :: 'a.
    logipedia_connectives_equal x y \<longrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"
  sorry

end
