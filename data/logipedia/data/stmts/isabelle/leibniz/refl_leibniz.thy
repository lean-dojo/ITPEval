(*
  Statement-only formalization of Logipedia corpus artifact
  leibniz.refl_leibniz, catalog title "leibniz.refl_leibniz": reflexivity of
  Leibniz equality, defined by preservation of every predicate on an arbitrary
  type. This file contains no proof.
*)

theory refl_leibniz
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

theorem leibniz_refl_leibniz:
  "\<forall>x :: 'a. logipedia_leibniz x x"
  sorry

end
