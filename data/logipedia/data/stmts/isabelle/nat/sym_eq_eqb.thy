(*
  Statement-only formalization of Logipedia corpus artifact nat.sym_eq_eqb,
  catalog title "nat.sym_eq_eqb": for every natural number, the filtered
  equality body is Leibniz-equal to the unary Boolean equality function.
  This file contains no proof.
*)

theory sym_eq_eqb
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

theorem sym_eq_eqb:
  "\<forall>n :: nat.
    logipedia_leibniz
      (filter_nat_type eqb_body n)
      (eqb n)"
  sorry

end
