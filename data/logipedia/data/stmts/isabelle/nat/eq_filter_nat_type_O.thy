(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_filter_nat_type_O, catalog title "nat.eq_filter_nat_type_O": for
  every result type and natural-number-indexed return function, filtering that
  function at zero is Leibniz-equal to its value at zero. This file contains
  no proof.
*)

theory eq_filter_nat_type_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"

theorem eq_filter_nat_type_O:
  "\<forall>ret :: nat \<Rightarrow> 'a.
    logipedia_leibniz
      (filter_nat_type ret 0)
      (ret 0)"
  sorry

end
