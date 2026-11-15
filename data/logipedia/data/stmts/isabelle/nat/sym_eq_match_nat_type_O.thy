(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_match_nat_type_O, catalog title
  "nat.sym_eq_match_nat_type_O": for every result type, zero branch, and
  successor branch over natural numbers, the zero branch is Leibniz-equal to
  the polymorphic natural-number matcher at zero. This file contains no proof.
*)

theory sym_eq_match_nat_type_O
  imports Main
begin

consts
  logipedia_match_nat_type ::
    "'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "logipedia_leibniz x y \<equiv>
      (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

theorem sym_eq_match_nat_type_O:
  "\<forall>case_O :: 'a. \<forall>case_S :: nat \<Rightarrow> 'a.
    logipedia_leibniz
      case_O
      (logipedia_match_nat_type case_O case_S 0)"
  sorry

end
