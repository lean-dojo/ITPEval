(*
  Statement-only formalization of Logipedia corpus artifact
  fact.sym_eq_fact_body_O, catalog title "fact.sym_eq_fact_body_O": the
  successor of zero is Leibniz-equal to the abstract factorial body at zero.
  This file contains no proof.
*)

theory sym_eq_fact_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  fact_body :: "nat \<Rightarrow> nat"

theorem sym_eq_fact_body_O:
  "logipedia_leibniz (Suc 0) (fact_body 0)"
  sorry

end
