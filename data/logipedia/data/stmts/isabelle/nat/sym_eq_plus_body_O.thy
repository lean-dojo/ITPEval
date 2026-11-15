(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_plus_body_O, catalog title "nat.sym_eq_plus_body_O": the identity
  function on natural numbers is Leibniz-equal to the abstract natural-number
  addition body at zero. This file contains no proof.
*)

theory sym_eq_plus_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  plus_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_plus_body_O:
  "logipedia_leibniz
    (\<lambda>m :: nat. m)
    (plus_body 0)"
  sorry

end
