(*
  Statement-only formalization of Logipedia corpus artifact exp.eq_exp_body_S,
  catalog title "exp.eq_exp_body_S": for every natural base and exponent, the
  abstract exponentiation body at the successor exponent is Leibniz-equal to
  the preceding abstract exponentiation value times the base. This file
  contains no proof.
*)

theory eq_exp_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  exp :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  exp_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_exp_body_S:
  "\<forall>n m :: nat.
    logipedia_leibniz
      (exp_body n (Suc m))
      (exp n m * n)"
  sorry

end
