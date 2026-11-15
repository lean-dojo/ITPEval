(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_leb,
  catalog title "nat.eq_leb": for every natural number, the unary Boolean
  less-than-or-equal function is Leibniz-equal to the corresponding filtered
  comparison body. This file contains no proof.
*)

theory eq_leb
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

theorem eq_leb:
  "\<forall>n :: nat.
    logipedia_leibniz
      (leb n)
      (filter_nat_type leb_body n)"
  sorry

end
