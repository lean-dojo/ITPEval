(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_match_nat_type_O, catalog title "nat.eq_match_nat_type_O": for every
  result type, zero branch, and successor branch over natural numbers, the
  polymorphic natural-number matcher at zero is Leibniz-equal to the zero
  branch. This file contains no proof.
*)

theory eq_match_nat_type_O
  imports Main
begin

consts
  logipedia_match_nat_type ::
    "'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "logipedia_leibniz x y \<equiv>
      (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

theorem eq_match_nat_type_O:
  "\<forall>case_O :: 'a. \<forall>case_S :: nat \<Rightarrow> 'a.
    logipedia_leibniz
      (logipedia_match_nat_type case_O case_S 0)
      case_O"
  sorry

end
