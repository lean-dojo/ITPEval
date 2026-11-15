(*
  Statement-only formalization of Logipedia corpus artifact exp.eq_exp,
  catalog title "exp.eq_exp": for all natural bases and exponents, the
  abstract exponentiation function is Leibniz-equal to the corresponding
  indexed exponentiation body. This file contains no proof.
*)

theory eq_exp
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

theorem eq_exp:
  "\<forall>n m :: nat.
    logipedia_leibniz
      (exp n m)
      (filter_nat_type (exp_body n) m)"
  sorry

end
