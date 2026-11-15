(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_times,
  catalog title "nat.eq_times": for every natural number, the unary
  multiplication function is Leibniz-equal to the corresponding filtered
  multiplication body. This file contains no proof.
*)

theory eq_times
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  times :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  times_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  filter_nat_type ::
    "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_times:
  "\<forall>n :: nat.
    logipedia_leibniz
      (times n)
      (filter_nat_type times_body n)"
  sorry

end
