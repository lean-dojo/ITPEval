(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_minus,
  catalog title "nat.eq_minus": for every natural number, the unary
  subtraction function is Leibniz-equal to the corresponding filtered
  subtraction body. This file contains no proof.
*)

theory eq_minus
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  minus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  minus_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  filter_nat_type ::
    "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_minus:
  "\<forall>n :: nat.
    logipedia_leibniz
      (minus n)
      (filter_nat_type minus_body n)"
  sorry

end
