(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_minus,
  catalog title "nat.axiom_minus": for every natural number, the unary
  subtraction function is related by the source equality predicate to the
  corresponding filtered subtraction body. This file contains no proof.
*)

theory axiom_minus
  imports Main
begin

consts
  logipedia_connectives_equal ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  minus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  minus_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  filter_nat_type ::
    "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_minus:
  "\<forall>n :: nat.
    logipedia_connectives_equal
      (minus n)
      (filter_nat_type minus_body n)"
  sorry

end
