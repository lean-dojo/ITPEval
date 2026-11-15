(*
  Statement-only formalization of Logipedia corpus artifact nat.sym_eq_times,
  catalog title "nat.sym_eq_times": for every natural number, the filtered
  multiplication body is Leibniz-equal to the unary multiplication function.
  This file contains no proof.
*)

theory sym_eq_times
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

theorem sym_eq_times:
  "\<forall>n :: nat.
    logipedia_leibniz
      (filter_nat_type times_body n)
      (times n)"
  sorry

end
