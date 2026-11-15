(*
  Statement-only formalization of Logipedia corpus artifact
  exp.sym_eq_exp_body_O, catalog title "exp.sym_eq_exp_body_O": for every
  natural base, the successor of zero is Leibniz-equal to the abstract
  exponentiation body at exponent zero. This file contains no proof.
*)

theory sym_eq_exp_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  exp_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_exp_body_O:
  "\<forall>n :: nat.
    logipedia_leibniz (Suc 0) (exp_body n 0)"
  sorry

end
