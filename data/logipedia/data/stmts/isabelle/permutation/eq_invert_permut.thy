(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.eq_invert_permut, catalog title
  "permutation.eq_invert_permut": for every natural number, the abstract
  inverse-permutation function is Leibniz-equal to the corresponding
  natural-number-filtered inverse-permutation body. This file contains no
  proof.
*)

theory eq_invert_permut
  imports Main
begin

definition filter_nat_type :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "filter_nat_type f n = f n"

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  invert_permut :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
  invert_permut_body ::
    "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_invert_permut:
  "\<forall>n :: nat.
    logipedia_leibniz
      (invert_permut n)
      (filter_nat_type invert_permut_body n)"
  sorry

end
