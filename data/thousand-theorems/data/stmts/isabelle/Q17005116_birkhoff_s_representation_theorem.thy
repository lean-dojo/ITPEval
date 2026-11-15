(*
  Statement-only formalization of thousand-theorems corpus artifact Q17005116
  (thousand-theorems__isabelle__Q17005116), "Birkhoff's representation
  theorem": the canonical map from a finite distributive lattice to the
  powerset of its sup-irreducible elements is an injective lattice
  homomorphism. This file contains no proof.
*)

theory Q17005116_birkhoff_s_representation_theorem
  imports Main
begin

definition q17005116_finite_distrib_lattice_on ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "q17005116_finite_distrib_lattice_on C meet join \<longleftrightarrow>
    finite C \<and>
    (\<forall>x \<in> C. \<forall>y \<in> C. meet x y \<in> C \<and> join x y \<in> C) \<and>
    (\<forall>x \<in> C. meet x x = x \<and> join x x = x) \<and>
    (\<forall>x \<in> C. \<forall>y \<in> C.
      meet x y = meet y x \<and> join x y = join y x) \<and>
    (\<forall>x \<in> C. \<forall>y \<in> C. \<forall>z \<in> C.
      meet (meet x y) z = meet x (meet y z) \<and>
      join (join x y) z = join x (join y z)) \<and>
    (\<forall>x \<in> C. \<forall>y \<in> C.
      meet x (join x y) = x \<and> join x (meet x y) = x) \<and>
    (\<forall>x \<in> C. \<forall>y \<in> C. \<forall>z \<in> C.
      meet x (join y z) = join (meet x y) (meet x z) \<and>
      join x (meet y z) = meet (join x y) (join x z))"

definition q17005116_sup_irreducible_on ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" where
  "q17005116_sup_irreducible_on C meet join x \<longleftrightarrow>
    x \<in> C \<and>
    \<not> (\<forall>y \<in> C. meet x y = x) \<and>
    (\<forall>y \<in> C. \<forall>z \<in> C. join y z = x \<longrightarrow> y = x \<or> z = x)"

definition q17005116_birkhoff_set ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "q17005116_birkhoff_set C meet join x =
    {j \<in> C. q17005116_sup_irreducible_on C meet join j \<and> meet j x = j}"

theorem birkhoff_set_representation:
  fixes C :: "'a set"
    and meet join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes "q17005116_finite_distrib_lattice_on C meet join"
  shows
    "inj_on (q17005116_birkhoff_set C meet join) C \<and>
    (\<forall>x \<in> C.
      q17005116_birkhoff_set C meet join x
        \<subseteq> {j. q17005116_sup_irreducible_on C meet join j}) \<and>
    (\<forall>x \<in> C. \<forall>y \<in> C.
      q17005116_birkhoff_set C meet join (join x y) =
        q17005116_birkhoff_set C meet join x \<union>
        q17005116_birkhoff_set C meet join y \<and>
      q17005116_birkhoff_set C meet join (meet x y) =
        q17005116_birkhoff_set C meet join x \<inter>
        q17005116_birkhoff_set C meet join y)"
  sorry

end
