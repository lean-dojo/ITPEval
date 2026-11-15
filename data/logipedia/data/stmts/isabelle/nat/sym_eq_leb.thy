(*
  Statement-only formalization of Logipedia corpus artifact nat.sym_eq_leb,
  catalog title "nat.sym_eq_leb": for every natural number, the filtered
  less-than-or-equal body is Leibniz-equal to the unary Boolean
  less-than-or-equal function. This file contains no proof.
*)

theory sym_eq_leb
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  leb :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  leb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  filter_nat_type ::
    "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> bool"

theorem sym_eq_leb:
  "\<forall>n :: nat.
    logipedia_leibniz
      (filter_nat_type leb_body n)
      (leb n)"
  sorry

end
