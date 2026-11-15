(*
  Statement-only formalization of thousand-theorems corpus artifact Q2471737,
  "Carathéodory's theorem (convex hull)": over a linearly ordered field, the
  convex hull of a set is the union of the convex hulls of its finite
  affine-independent subsets. This file contains no proof.
*)

theory Q2471737_carath_odory_s_theorem_convex_hull
  imports Main
begin

definition q2471737_module ::
    "('k::field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q2471737_module smult \<longleftrightarrow>
    (\<forall>a x y. smult a (x + y) = smult a x + smult a y) \<and>
    (\<forall>a b x. smult (a + b) x = smult a x + smult b x) \<and>
    (\<forall>a b x. smult (a * b) x = smult a (smult b x)) \<and>
    (\<forall>x. smult 1 x = x)"

definition q2471737_affine_independent ::
    "('k::field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
      'e set \<Rightarrow> bool" where
  "q2471737_affine_independent smult T \<longleftrightarrow>
    (\<forall>w :: 'e \<Rightarrow> 'k.
      finite {y. w y \<noteq> 0} \<longrightarrow>
      {y. w y \<noteq> 0} \<subseteq> T \<longrightarrow>
      (\<Sum>y\<in>{y. w y \<noteq> 0}. w y) = 0 \<longrightarrow>
      (\<Sum>y\<in>{y. w y \<noteq> 0}. smult (w y) y) = 0 \<longrightarrow>
      (\<forall>y. w y = 0))"

definition q2471737_convex_hull ::
    "('k::linordered_field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
      'e set \<Rightarrow> 'e set" where
  "q2471737_convex_hull smult S =
    {x. \<exists>w :: 'e \<Rightarrow> 'k.
      finite {y. w y \<noteq> 0} \<and>
      {y. w y \<noteq> 0} \<subseteq> S \<and>
      (\<forall>y. 0 \<le> w y) \<and>
      (\<Sum>y\<in>{y. w y \<noteq> 0}. w y) = 1 \<and>
      (\<Sum>y\<in>{y. w y \<noteq> 0}. smult (w y) y) = x}"

theorem convexHull_eq_union:
  fixes smult :: "'k::linordered_field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e"
    and S :: "'e set"
  assumes module: "q2471737_module smult"
  shows "q2471737_convex_hull smult S =
    {x. \<exists>T :: 'e set.
      finite T \<and>
      T \<subseteq> S \<and>
      q2471737_affine_independent smult T \<and>
      x \<in> q2471737_convex_hull smult T}"
  sorry

end
