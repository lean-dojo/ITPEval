(*
  Statement-only formalization of thousand-theorems corpus artifact Q505798
  (thousand-theorems__isabelle__Q505798), "Lagrange's theorem (group theory)":
  the cardinality of any subgroup of an arbitrary multiplicative group divides
  the cardinality of the ambient group. This file contains no proof.
*)

theory Q505798_lagrange_s_theorem_group_theory
  imports Main
begin

definition q505798_is_group ::
    "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> bool" where
  "q505798_is_group mul e inverse_op \<longleftrightarrow>
    (\<forall>x y z. mul (mul x y) z = mul x (mul y z)) \<and>
    (\<forall>x. mul e x = x \<and> mul x e = x) \<and>
    (\<forall>x. mul (inverse_op x) x = e \<and> mul x (inverse_op x) = e)"

definition q505798_is_subgroup ::
    "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow>
      ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> bool" where
  "q505798_is_subgroup mul e inverse_op H \<longleftrightarrow>
    e \<in> H \<and>
    (\<forall>x \<in> H. inverse_op x \<in> H) \<and>
    (\<forall>x \<in> H. \<forall>y \<in> H. mul x y \<in> H)"

theorem q505798_card_subgroup_dvd_card:
  fixes mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: "'g"
    and inverse_op :: "'g \<Rightarrow> 'g"
    and H :: "'g set"
  assumes ambient_group: "q505798_is_group mul e inverse_op"
    and subgroup_H: "q505798_is_subgroup mul e inverse_op H"
  shows "card H dvd card (UNIV :: 'g set)"
  sorry

end
