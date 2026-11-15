(*
  Statement-only formalization of the thousand-theorems corpus artifact Q7525341
  (thousand-theorems__isabelle__Q7525341), "Sion's minimax theorem": for a
  compact nonempty convex set X and a convex set Y in real topological vector
  spaces, lower-semicontinuous quasiconvex sections in X and
  upper-semicontinuous quasiconcave sections in Y identify the specified
  infimum-of-suprema and supremum-of-infima in a linearly ordered codomain.
  This file contains no proof.
*)

theory Q7525341_sion_s_minimax_theorem
  imports Complex_Main
begin

definition q7525341_convex :: "'a::real_vector set \<Rightarrow> bool"
  where
    "q7525341_convex S \<longleftrightarrow>
      (\<forall>x \<in> S. \<forall>y \<in> S. \<forall>u \<ge> 0. \<forall>v \<ge> 0.
        u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> S)"

definition q7525341_lower_semicontinuous_on ::
    "('a::topological_space \<Rightarrow> 'b::preorder) \<Rightarrow> 'a set \<Rightarrow> bool"
  where
    "q7525341_lower_semicontinuous_on g S \<longleftrightarrow>
      (\<forall>x \<in> S. \<forall>b < g x.
        eventually (\<lambda>z. b < g z) (inf (nhds x) (principal S)))"

definition q7525341_upper_semicontinuous_on ::
    "('a::topological_space \<Rightarrow> 'b::preorder) \<Rightarrow> 'a set \<Rightarrow> bool"
  where
    "q7525341_upper_semicontinuous_on g S \<longleftrightarrow>
      (\<forall>x \<in> S. \<forall>b. g x < b \<longrightarrow>
        eventually (\<lambda>z. g z < b) (inf (nhds x) (principal S)))"

definition q7525341_quasiconvex_on ::
    "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> 'b::preorder) \<Rightarrow> bool"
  where
    "q7525341_quasiconvex_on S g \<longleftrightarrow>
      (\<forall>b. q7525341_convex {x \<in> S. g x \<le> b})"

definition q7525341_quasiconcave_on ::
    "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> 'b::preorder) \<Rightarrow> bool"
  where
    "q7525341_quasiconcave_on S g \<longleftrightarrow>
      (\<forall>b. q7525341_convex {x \<in> S. b \<le> g x})"

definition q7525341_is_lub :: "'a::order set \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "q7525341_is_lub S a \<longleftrightarrow>
      (\<forall>x \<in> S. x \<le> a) \<and>
      (\<forall>u. (\<forall>x \<in> S. x \<le> u) \<longrightarrow> a \<le> u)"

definition q7525341_is_glb :: "'a::order set \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "q7525341_is_glb S a \<longleftrightarrow>
      (\<forall>x \<in> S. a \<le> x) \<and>
      (\<forall>l. (\<forall>x \<in> S. l \<le> x) \<longrightarrow> l \<le> a)"

theorem q7525341_sion_minimax:
  fixes X :: "'e::{real_vector,topological_ab_group_add} set"
    and Y :: "'f::{real_vector,topological_ab_group_add} set"
    and f :: "'e \<Rightarrow> 'f \<Rightarrow> 'b::linorder"
    and sup_y :: "'e \<Rightarrow> 'b"
    and inf_sup :: "'b"
    and inf_x :: "'f \<Rightarrow> 'b"
    and sup_inf :: "'b"
  assumes continuous_scale_e:
      "continuous_on UNIV (\<lambda>p :: real \<times> 'e. fst p *\<^sub>R snd p)"
    and nonempty_X: "X \<noteq> {}"
    and compact_X: "compact X"
    and lower_semicontinuous:
      "\<forall>y \<in> Y. q7525341_lower_semicontinuous_on (\<lambda>x. f x y) X"
    and quasiconvex:
      "\<forall>y \<in> Y. q7525341_quasiconvex_on X (\<lambda>x. f x y)"
    and continuous_scale_f:
      "continuous_on UNIV (\<lambda>p :: real \<times> 'f. fst p *\<^sub>R snd p)"
    and convex_Y: "q7525341_convex Y"
    and upper_semicontinuous:
      "\<forall>x \<in> X. q7525341_upper_semicontinuous_on (f x) Y"
    and quasiconcave:
      "\<forall>x \<in> X. q7525341_quasiconcave_on Y (f x)"
    and convex_X: "q7525341_convex X"
    and sup_y_is_lub:
      "\<forall>x \<in> X. q7525341_is_lub ((f x) ` Y) (sup_y x)"
    and inf_sup_is_glb:
      "q7525341_is_glb (sup_y ` X) inf_sup"
    and inf_x_is_glb:
      "\<forall>y \<in> Y. q7525341_is_glb ((\<lambda>x. f x y) ` X) (inf_x y)"
    and sup_inf_is_lub:
      "q7525341_is_lub (inf_x ` Y) sup_inf"
  shows "inf_sup = sup_inf"
  sorry

end
