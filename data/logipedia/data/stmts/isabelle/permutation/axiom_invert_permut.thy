(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.axiom_invert_permut, catalog title
  "permutation.axiom_invert_permut": for every natural number, the abstract
  inverse-permutation function is related by the source equality predicate to
  the natural-number-filtered inverse-permutation body. This file contains no
  proof.
*)

theory axiom_invert_permut
  imports Main
begin

consts
  logipedia_connectives_equal ::
    "((nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
      ((nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> bool"
  invert_permut :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
  invert_permut_body ::
    "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
  filter_nat_type ::
    "(nat \<Rightarrow> ((nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat)) \<Rightarrow>
      nat \<Rightarrow> ((nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat)"

theorem axiom_invert_permut:
  "\<forall>n :: nat.
    logipedia_connectives_equal
      (invert_permut n)
      (filter_nat_type invert_permut_body n)"
  sorry

end
