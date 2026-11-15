(*
  Statement-only formalization of Logipedia corpus artifact nat.sym_eq_plus,
  catalog title "nat.sym_eq_plus": for every natural number, the filtered
  addition body is Leibniz-equal to the unary addition function. This file
  contains no proof.
*)

theory sym_eq_plus
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  plus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  plus_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  filter_nat_type ::
    "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_plus:
  "\<forall>n :: nat.
    logipedia_leibniz
      (filter_nat_type plus_body n)
      (plus n)"
  sorry

end
