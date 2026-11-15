(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_leb,
  catalog title "nat.axiom_leb": for every natural number, the unary Boolean
  less-than-or-equal function is related by the source equality predicate to
  the corresponding filtered comparison body. This file contains no proof.
*)

theory axiom_leb
  imports Main
begin

consts
  logipedia_connectives_equal ::
    "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool"
  leb :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  leb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  filter_nat_type ::
    "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> bool"

theorem axiom_leb:
  "\<forall>n :: nat.
    logipedia_connectives_equal
      (leb n)
      (filter_nat_type leb_body n)"
  sorry

end
