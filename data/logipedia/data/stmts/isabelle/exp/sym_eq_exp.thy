(*
  Statement-only formalization of Logipedia corpus artifact exp.sym_eq_exp,
  catalog title "exp.sym_eq_exp": for all natural bases and exponents, the
  corresponding indexed exponentiation body is Leibniz-equal to the abstract
  exponentiation function. This file contains no proof.
*)

theory sym_eq_exp
  imports Main
begin

definition filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "filter_nat_type f m = f m"

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  exp :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  exp_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_exp:
  "\<forall>n m :: nat.
    logipedia_leibniz
      (filter_nat_type (exp_body n) m)
      (exp n m)"
  sorry

end
