(*
  Statement-only formalization of thousand-theorems corpus artifact Q1471282,
  "Radon's theorem": every affinely dependent family over a linearly ordered
  field admits a partition of its index set whose two image sets have
  intersecting convex hulls. This file contains no proof.
*)

theory Q1471282_radon_s_theorem
  imports Main
begin

definition q1471282_module ::
    "('k::field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1471282_module smult \<longleftrightarrow>
    (\<forall>a x y. smult a (x + y) = smult a x + smult a y) \<and>
    (\<forall>a b x. smult (a + b) x = smult a x + smult b x) \<and>
    (\<forall>a b x. smult (a * b) x = smult a (smult b x)) \<and>
    (\<forall>x. smult 1 x = x)"

definition q1471282_affine_independent ::
    "('k::field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
      ('i \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1471282_affine_independent smult f \<longleftrightarrow>
    (\<forall>w :: 'i \<Rightarrow> 'k.
      finite {i. w i \<noteq> 0} \<longrightarrow>
      (\<Sum>i\<in>{i. w i \<noteq> 0}. w i) = 0 \<longrightarrow>
      (\<Sum>i\<in>{i. w i \<noteq> 0}. smult (w i) (f i)) = 0 \<longrightarrow>
      (\<forall>i. w i = 0))"

definition q1471282_convex_hull ::
    "('k::linordered_field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
      'e set \<Rightarrow> 'e set" where
  "q1471282_convex_hull smult S =
    {x. \<exists>w :: 'e \<Rightarrow> 'k.
      finite {y. w y \<noteq> 0} \<and>
      {y. w y \<noteq> 0} \<subseteq> S \<and>
      (\<forall>y. 0 \<le> w y) \<and>
      (\<Sum>y\<in>{y. w y \<noteq> 0}. w y) = 1 \<and>
      (\<Sum>y\<in>{y. w y \<noteq> 0}. smult (w y) y) = x}"

theorem radon_partition:
  fixes smult :: "'k::linordered_field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e"
    and f :: "'i \<Rightarrow> 'e"
  assumes module: "q1471282_module smult"
    and affine_dependent: "\<not> q1471282_affine_independent smult f"
  shows "\<exists>I :: 'i set.
    q1471282_convex_hull smult (f ` I) \<inter>
      q1471282_convex_hull smult (f ` (UNIV - I)) \<noteq> {}"
  sorry

end
