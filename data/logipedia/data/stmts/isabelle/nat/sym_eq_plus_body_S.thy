(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_plus_body_S, catalog title "nat.sym_eq_plus_body_S": for every
  value of the abstract natural-number type, the function mapping each value
  to the successor of its abstract sum with the original value is
  Leibniz-equal to the abstract addition body at the successor. This file
  contains no proof.
*)

theory sym_eq_plus_body_S
  imports Main
begin

typedecl logipedia_nat

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  logipedia_S :: "logipedia_nat \<Rightarrow> logipedia_nat"
  logipedia_plus ::
    "logipedia_nat \<Rightarrow> logipedia_nat \<Rightarrow> logipedia_nat"
  logipedia_plus_body ::
    "logipedia_nat \<Rightarrow> logipedia_nat \<Rightarrow> logipedia_nat"

theorem sym_eq_plus_body_S:
  "\<forall>n :: logipedia_nat.
    logipedia_leibniz
      (\<lambda>m :: logipedia_nat. logipedia_S (logipedia_plus n m))
      (logipedia_plus_body (logipedia_S n))"
  sorry

end
