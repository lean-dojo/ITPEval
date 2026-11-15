(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_filter_nat_type_O, catalog title
  "nat.sym_eq_filter_nat_type_O": for every result type and function on
  natural numbers, its value at zero is Leibniz-equal to the polymorphic
  natural-number filter applied at zero. This file contains no proof.
*)

theory sym_eq_filter_nat_type_O
  imports Main
begin

consts logipedia_filter_nat_type ::
  "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "logipedia_leibniz x y \<equiv>
      (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

theorem sym_eq_filter_nat_type_O:
  "\<forall>return_fn :: nat \<Rightarrow> 'a.
    logipedia_leibniz
      (return_fn 0)
      (logipedia_filter_nat_type return_fn 0)"
  sorry

end
