(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_times,
  catalog title "nat.axiom_times": for every natural number, the unary
  multiplication function is related by the source equality predicate to the
  corresponding filtered multiplication body. This file contains no proof.
*)

theory axiom_times
  imports Main
begin

consts
  logipedia_connectives_equal ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  times :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  times_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  filter_nat_type ::
    "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_times:
  "\<forall>n :: nat.
    logipedia_connectives_equal
      (times n)
      (filter_nat_type times_body n)"
  sorry

end
