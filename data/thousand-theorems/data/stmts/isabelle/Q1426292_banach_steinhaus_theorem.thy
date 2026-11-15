(*
  Statement-only formalization of thousand-theorems corpus artifact Q1426292,
  "Banach–Steinhaus theorem": a pointwise bounded family of continuous
  semilinear maps from a complete seminormed space to a seminormed space has
  uniformly bounded operator norms. This file contains no proof.
*)

theory Q1426292_banach_steinhaus_theorem
  imports Complex_Main
begin

definition q1426292_nontrivially_normed_field ::
    "('k::field \<Rightarrow> real) \<Rightarrow> bool" where
  "q1426292_nontrivially_normed_field knorm \<longleftrightarrow>
    knorm 0 = 0 \<and>
    (\<forall>a. 0 \<le> knorm a) \<and>
    (\<forall>a. knorm a = 0 \<longleftrightarrow> a = 0) \<and>
    (\<forall>a. knorm (-a) = knorm a) \<and>
    (\<forall>a b. knorm (a + b) \<le> knorm a + knorm b) \<and>
    (\<forall>a b. knorm (a * b) = knorm a * knorm b) \<and>
    (\<exists>a. 1 < knorm a)"

definition q1426292_seminormed_add_comm_group ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow> bool" where
  "q1426292_seminormed_add_comm_group enorm \<longleftrightarrow>
    enorm 0 = 0 \<and>
    (\<forall>x. 0 \<le> enorm x) \<and>
    (\<forall>x. enorm (-x) = enorm x) \<and>
    (\<forall>x y. enorm (x + y) \<le> enorm x + enorm y)"

definition q1426292_normed_space ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
     ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1426292_normed_space knorm enorm scale \<longleftrightarrow>
    (\<forall>a x y. scale a (x + y) = scale a x + scale a y) \<and>
    (\<forall>a b x. scale (a + b) x = scale a x + scale b x) \<and>
    (\<forall>a b x. scale (a * b) x = scale a (scale b x)) \<and>
    (\<forall>x. scale 1 x = x) \<and>
    (\<forall>a x. enorm (scale a x) = knorm a * enorm x)"

definition q1426292_isometric_ring_hom ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
     ('l::field \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'l) \<Rightarrow> bool" where
  "q1426292_isometric_ring_hom knorm lnorm sigma \<longleftrightarrow>
    sigma 0 = 0 \<and>
    sigma 1 = 1 \<and>
    (\<forall>a b. sigma (a + b) = sigma a + sigma b) \<and>
    (\<forall>a b. sigma (a * b) = sigma a * sigma b) \<and>
    (\<forall>a. lnorm (sigma a) = knorm a)"

definition q1426292_complete_in_seminorm ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow> bool" where
  "q1426292_complete_in_seminorm enorm \<longleftrightarrow>
    (\<forall>u :: nat \<Rightarrow> 'e.
      (\<forall>epsilon > 0. \<exists>N. \<forall>m \<ge> N. \<forall>n \<ge> N.
        enorm (u m - u n) < epsilon) \<longrightarrow>
      (\<exists>x. \<forall>epsilon > 0. \<exists>N. \<forall>n \<ge> N.
        enorm (u n - x) < epsilon))"

definition q1426292_continuous_semilinear ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
     ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
     ('k::field \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
     ('l::field \<Rightarrow> 'f \<Rightarrow> 'f) \<Rightarrow>
     ('k \<Rightarrow> 'l) \<Rightarrow>
     ('e \<Rightarrow> 'f) \<Rightarrow> bool" where
  "q1426292_continuous_semilinear enorm fnorm escale fscale sigma T \<longleftrightarrow>
    (\<forall>x y. T (x + y) = T x + T y) \<and>
    (\<forall>a x. T (escale a x) = fscale (sigma a) (T x)) \<and>
    (\<forall>x epsilon. 0 < epsilon \<longrightarrow>
      (\<exists>delta > 0. \<forall>y.
        enorm (y - x) < delta \<longrightarrow>
        fnorm (T y - T x) < epsilon))"

definition q1426292_operator_norm ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
     ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
     ('e \<Rightarrow> 'f) \<Rightarrow> real" where
  "q1426292_operator_norm enorm fnorm T =
    Inf {C. 0 \<le> C \<and> (\<forall>x. fnorm (T x) \<le> C * enorm x)}"

theorem banach_steinhaus:
  fixes knorm :: "'k::field \<Rightarrow> real"
    and lnorm :: "'l::field \<Rightarrow> real"
    and enorm :: "'e::ab_group_add \<Rightarrow> real"
    and fnorm :: "'f::ab_group_add \<Rightarrow> real"
    and escale :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and fscale :: "'l \<Rightarrow> 'f \<Rightarrow> 'f"
    and sigma :: "'k \<Rightarrow> 'l"
    and g :: "'i \<Rightarrow> 'e \<Rightarrow> 'f"
  assumes "q1426292_nontrivially_normed_field knorm"
    and "q1426292_nontrivially_normed_field lnorm"
    and "q1426292_seminormed_add_comm_group enorm"
    and "q1426292_seminormed_add_comm_group fnorm"
    and "q1426292_normed_space knorm enorm escale"
    and "q1426292_normed_space lnorm fnorm fscale"
    and "q1426292_isometric_ring_hom knorm lnorm sigma"
    and "q1426292_complete_in_seminorm enorm"
    and "\<forall>i.
      q1426292_continuous_semilinear enorm fnorm escale fscale sigma (g i)"
    and "\<forall>x. \<exists>C. \<forall>i. fnorm (g i x) \<le> C"
  shows "\<exists>C'. \<forall>i.
    q1426292_operator_norm enorm fnorm (g i) \<le> C'"
  sorry

end
