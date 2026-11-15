(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_plus,
  catalog title "nat.axiom_plus": for every natural number, the unary addition
  function is related by the source equality predicate to the corresponding
  filtered addition body. This file contains no proof.
*)

theory axiom_plus
  imports Main
begin

consts
  logipedia_connectives_equal ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  plus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  plus_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  filter_nat_type ::
    "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_plus:
  "\<forall>n :: nat.
    logipedia_connectives_equal
      (plus n)
      (filter_nat_type plus_body n)"
  sorry

end
