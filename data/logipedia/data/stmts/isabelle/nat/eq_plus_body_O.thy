(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_plus_body_O, catalog title "nat.eq_plus_body_O": the abstract
  natural-number addition body at zero is Leibniz-equal to the identity
  function. This file contains no proof.
*)

theory eq_plus_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  plus_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_plus_body_O:
  "logipedia_leibniz
    (plus_body 0)
    (\<lambda>m :: nat. m)"
  sorry

end
