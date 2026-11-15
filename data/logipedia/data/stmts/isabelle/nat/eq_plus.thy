(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_plus,
  catalog title "nat.eq_plus": for every natural number, the unary addition
  function is Leibniz-equal to the corresponding filtered addition body.
  This file contains no proof.
*)

theory eq_plus
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

theorem eq_plus:
  "\<forall>n :: nat.
    logipedia_leibniz
      (plus n)
      (filter_nat_type plus_body n)"
  sorry

end
