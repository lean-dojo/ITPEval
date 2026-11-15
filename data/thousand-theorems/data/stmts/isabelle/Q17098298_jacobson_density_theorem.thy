(*
  Statement-only formalization of thousand-theorems corpus artifact Q17098298
  (thousand-theorems__isabelle__Q17098298), "Jacobson density theorem": for a
  semisimple left module over an arbitrary unital ring, every additive
  self-map commuting with all module endomorphisms agrees on any finite set
  with scalar multiplication by one ring element. This file contains no proof.
*)

theory Q17098298_jacobson_density_theorem
  imports Main
begin

definition q17098298_unital_ring ::
    "'r::ring \<Rightarrow> bool" where
  "q17098298_unital_ring oneR \<longleftrightarrow>
    (\<forall>a. oneR * a = a) \<and>
    (\<forall>a. a * oneR = a)"

definition q17098298_module ::
    "'r::ring \<Rightarrow> ('r \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm) \<Rightarrow> bool" where
  "q17098298_module oneR smul \<longleftrightarrow>
    (\<forall>a b x. smul (a + b) x = smul a x + smul b x) \<and>
    (\<forall>a x y. smul a (x + y) = smul a x + smul a y) \<and>
    (\<forall>x. smul 0 x = 0) \<and>
    (\<forall>a. smul a 0 = 0) \<and>
    (\<forall>a b x. smul (a * b) x = smul a (smul b x)) \<and>
    (\<forall>x. smul oneR x = x)"

definition q17098298_submodule ::
    "('r::ring \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm) \<Rightarrow>
      'm set \<Rightarrow> bool" where
  "q17098298_submodule smul N \<longleftrightarrow>
    0 \<in> N \<and>
    (\<forall>x \<in> N. -x \<in> N) \<and>
    (\<forall>x \<in> N. \<forall>y \<in> N. x + y \<in> N) \<and>
    (\<forall>a. \<forall>x \<in> N. smul a x \<in> N)"

definition q17098298_semisimple_module ::
    "('r::ring \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm) \<Rightarrow> bool" where
  "q17098298_semisimple_module smul \<longleftrightarrow>
    (\<forall>N. q17098298_submodule smul N \<longrightarrow>
      (\<exists>P.
        q17098298_submodule smul P \<and>
        N \<inter> P = {0} \<and>
        (\<forall>x. \<exists>n \<in> N. \<exists>p \<in> P. x = n + p)))"

definition q17098298_additive_map ::
    "('m::ab_group_add \<Rightarrow> 'm) \<Rightarrow> bool" where
  "q17098298_additive_map f \<longleftrightarrow>
    f 0 = 0 \<and>
    (\<forall>x y. f (x + y) = f x + f y)"

definition q17098298_module_endomorphism ::
    "('r::ring \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm) \<Rightarrow>
      ('m \<Rightarrow> 'm) \<Rightarrow> bool" where
  "q17098298_module_endomorphism smul g \<longleftrightarrow>
    q17098298_additive_map g \<and>
    (\<forall>a x. g (smul a x) = smul a (g x))"

definition q17098298_endomorphism_linear_map ::
    "('r::ring \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm) \<Rightarrow>
      ('m \<Rightarrow> 'm) \<Rightarrow> bool" where
  "q17098298_endomorphism_linear_map smul f \<longleftrightarrow>
    q17098298_additive_map f \<and>
    (\<forall>g. q17098298_module_endomorphism smul g \<longrightarrow>
      (\<forall>x. f (g x) = g (f x)))"

theorem q17098298_jacobson_density:
  fixes oneR :: "'r::ring"
    and smul :: "'r \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm"
    and f :: "'m \<Rightarrow> 'm"
    and S :: "'m set"
  assumes ring_with_one: "q17098298_unital_ring oneR"
    and module: "q17098298_module oneR smul"
    and semisimple: "q17098298_semisimple_module smul"
    and endomorphism_linear:
      "q17098298_endomorphism_linear_map smul f"
    and finite_set: "finite S"
  shows "\<exists>r. \<forall>m \<in> S. f m = smul r m"
  sorry

end
