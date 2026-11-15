(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.sym_eq_gcd_aux, catalog title "gcd.sym_eq_gcd_aux": for every natural
  index, the corresponding indexed gcd body is Leibniz-equal to the abstract
  auxiliary gcd function as a curried function on natural numbers. This file
  contains no proof.
*)

theory sym_eq_gcd_aux
  imports Main
begin

definition filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "filter_nat_type f p = f p"

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  gcd_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  gcd_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_gcd_aux:
  "\<forall>p :: nat.
    logipedia_leibniz
      (filter_nat_type gcd_aux_body p)
      (gcd_aux p :: nat \<Rightarrow> nat \<Rightarrow> nat)"
  sorry

end
