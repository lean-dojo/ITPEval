(*
  Statement-only formalization of Logipedia corpus artifact
  fact.eq_fact_body_O, catalog title "fact.eq_fact_body_O": the abstract
  factorial body at zero is Leibniz-equal to the successor of zero. This file
  contains no proof.
*)

theory eq_fact_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  fact_body :: "nat \<Rightarrow> nat"

theorem eq_fact_body_O:
  "logipedia_leibniz (fact_body 0) (Suc 0)"
  sorry

end
