(*
  Statement-only formalization of Logipedia corpus artifact exp.eq_exp_body_O,
  catalog title "exp.eq_exp_body_O": for every natural base, the abstract
  exponentiation body at exponent zero is Leibniz-equal to the successor of
  zero. This file contains no proof.
*)

theory eq_exp_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  exp_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_exp_body_O:
  "\<forall>n :: nat.
    logipedia_leibniz (exp_body n 0) (Suc 0)"
  sorry

end
