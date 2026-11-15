(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.sym_eq_div_aux, catalog title "div_mod.sym_eq_div_aux": for every
  natural index, the indexed auxiliary division body is Leibniz-equal to the
  auxiliary division function as a curried function on natural numbers. This
  file contains no proof.
*)

theory sym_eq_div_aux
  imports Main
begin

definition filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "filter_nat_type f p = f p"

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  div_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  div_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_div_aux:
  "\<forall>p :: nat.
    logipedia_leibniz
      (filter_nat_type div_aux_body p)
      (div_aux p :: nat \<Rightarrow> nat \<Rightarrow> nat)"
  sorry

end
