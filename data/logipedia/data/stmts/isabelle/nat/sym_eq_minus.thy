(*
  Statement-only formalization of Logipedia corpus artifact nat.sym_eq_minus,
  catalog title "nat.sym_eq_minus": for every natural number, the filtered
  subtraction body is Leibniz-equal to the unary subtraction function.
  This file contains no proof.
*)

theory sym_eq_minus
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

theorem sym_eq_minus:
  "\<forall>n :: nat.
    logipedia_leibniz
      (filter_nat_type minus_body n)
      (minus n)"
  sorry

end
