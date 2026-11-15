(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.sym_eq_invert_permut, catalog title
  "permutation.sym_eq_invert_permut": for every natural number, the
  natural-number-filtered inverse-permutation body is Leibniz-equal to the
  corresponding abstract inverse-permutation function. This file contains no
  proof.
*)

theory sym_eq_invert_permut
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

theorem sym_eq_invert_permut:
  "\<forall>n :: nat.
    logipedia_leibniz
      (filter_nat_type invert_permut_body n)
      (invert_permut n)"
  sorry

end
