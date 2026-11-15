(*
  Statement-only formalization of Logipedia corpus artifact
  leibniz.sym_leibniz, catalog title "leibniz.sym_leibniz": symmetry of
  Leibniz equality, defined by preservation of every predicate on an arbitrary
  type. This file contains no proof.
*)

theory sym_leibniz
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

theorem leibniz_sym_leibniz:
  "\<forall>x y :: 'a.
    logipedia_leibniz x y \<longrightarrow> logipedia_leibniz y x"
  sorry

end
