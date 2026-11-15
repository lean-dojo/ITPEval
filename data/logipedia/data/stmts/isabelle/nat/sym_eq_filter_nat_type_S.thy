(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_filter_nat_type_S, catalog title "nat.sym_eq_filter_nat_type_S":
  for every result type, natural-number-indexed return function, and natural
  number, the function's value at the successor is Leibniz-equal to filtering
  that function at the successor. This file contains no proof.
*)

theory sym_eq_filter_nat_type_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"

theorem sym_eq_filter_nat_type_S:
  "\<forall>ret :: nat \<Rightarrow> 'a. \<forall>n :: nat.
    logipedia_leibniz
      (ret (Suc n))
      (filter_nat_type ret (Suc n))"
  sorry

end
