(*
  Statement-only formalization of Logipedia corpus artifact
  exp.sym_eq_exp_body_S, catalog title "exp.sym_eq_exp_body_S": for every
  natural base and exponent, the preceding abstract exponentiation value
  times the base is Leibniz-equal to the abstract exponentiation body at the
  successor exponent. This file contains no proof.
*)

theory sym_eq_exp_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  exp :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  exp_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_exp_body_S:
  "\<forall>n m :: nat.
    logipedia_leibniz
      (exp n m * n)
      (exp_body n (Suc m))"
  sorry

end
