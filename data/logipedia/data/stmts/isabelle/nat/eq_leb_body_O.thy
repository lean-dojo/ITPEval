(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_leb_body_O, catalog title "nat.eq_leb_body_O": the abstract Boolean
  less-than-or-equal body at zero is Leibniz-equal to the constant-true
  function on natural numbers. This file contains no proof.
*)

theory eq_leb_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts leb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"

theorem eq_leb_body_O:
  "logipedia_leibniz
    (leb_body 0 :: nat \<Rightarrow> bool)
    (\<lambda>m :: nat. True)"
  sorry

end
