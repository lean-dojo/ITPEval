(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_eqb,
  catalog title "nat.eq_eqb": for every natural number, the unary Boolean
  equality function is Leibniz-equal to the corresponding filtered equality
  body. This file contains no proof.
*)

theory eq_eqb
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  eqb :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  eqb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  filter_nat_type ::
    "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> bool"

theorem eq_eqb:
  "\<forall>n :: nat.
    logipedia_leibniz
      (eqb n)
      (filter_nat_type eqb_body n)"
  sorry

end
