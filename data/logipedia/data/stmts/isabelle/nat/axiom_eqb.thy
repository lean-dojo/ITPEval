(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_eqb,
  catalog title "nat.axiom_eqb": for every natural number, the unary
  Boolean equality function is related by the source equality predicate to
  the corresponding filtered equality body. This file contains no proof.
*)

theory axiom_eqb
  imports Main
begin

consts
  logipedia_connectives_equal ::
    "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool"
  eqb :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  eqb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  filter_nat_type ::
    "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> bool"

theorem axiom_eqb:
  "\<forall>n :: nat.
    logipedia_connectives_equal
      (eqb n)
      (filter_nat_type eqb_body n)"
  sorry

end
