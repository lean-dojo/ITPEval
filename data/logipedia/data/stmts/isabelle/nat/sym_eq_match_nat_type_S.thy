(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_match_nat_type_S, catalog title "nat.sym_eq_match_nat_type_S":
  for every result type, zero branch, successor branch, and natural number,
  the successor branch applied to that number is Leibniz-equal to the
  polymorphic natural-number matcher at its successor. This file contains no
  proof.
*)

theory sym_eq_match_nat_type_S
  imports Main
begin

typedecl logipedia_nat

consts
  logipedia_S :: "logipedia_nat \<Rightarrow> logipedia_nat"
  logipedia_match_nat_type ::
    "'a \<Rightarrow> (logipedia_nat \<Rightarrow> 'a) \<Rightarrow>
      logipedia_nat \<Rightarrow> 'a"

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "logipedia_leibniz x y \<equiv>
      (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

theorem sym_eq_match_nat_type_S:
  "\<forall>case_O :: 'a.
    \<forall>case_S :: logipedia_nat \<Rightarrow> 'a.
    \<forall>n :: logipedia_nat.
      logipedia_leibniz
        (case_S n)
        (logipedia_match_nat_type case_O case_S (logipedia_S n))"
  sorry

end
