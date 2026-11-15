(*
  Statement-only formalization of thousand-theorems corpus artifact Q944297,
  "Open mapping theorem (functional analysis)": a surjective continuous
  semilinear map between Banach spaces over isometrically equivalent
  nontrivially normed fields is an open map. This file contains no proof.
*)

theory Q944297_open_mapping_theorem_functional_analysis
  imports Complex_Main
begin

definition q944297_nontrivially_normed_field ::
    "('k::{field,metric_space} \<Rightarrow> real) \<Rightarrow> bool" where
  "q944297_nontrivially_normed_field knorm \<longleftrightarrow>
    knorm 0 = 0 \<and>
    (\<forall>a. 0 \<le> knorm a) \<and>
    (\<forall>a. knorm a = 0 \<longleftrightarrow> a = 0) \<and>
    (\<forall>a. knorm (-a) = knorm a) \<and>
    (\<forall>a b. knorm (a + b) \<le> knorm a + knorm b) \<and>
    (\<forall>a b. knorm (a * b) = knorm a * knorm b) \<and>
    (\<forall>a b. dist a b = knorm (a - b)) \<and>
    (\<exists>a. 1 < knorm a)"

definition q944297_normed_space ::
    "('k::{field,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('e::{ab_group_add,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q944297_normed_space knorm enorm scale \<longleftrightarrow>
    enorm 0 = 0 \<and>
    (\<forall>x. 0 \<le> enorm x) \<and>
    (\<forall>x. enorm x = 0 \<longleftrightarrow> x = 0) \<and>
    (\<forall>x. enorm (-x) = enorm x) \<and>
    (\<forall>x y. enorm (x + y) \<le> enorm x + enorm y) \<and>
    (\<forall>x y. dist x y = enorm (x - y)) \<and>
    (\<forall>a x y. scale a (x + y) = scale a x + scale a y) \<and>
    (\<forall>a b x. scale (a + b) x = scale a x + scale b x) \<and>
    (\<forall>a b x. scale (a * b) x = scale a (scale b x)) \<and>
    (\<forall>x. scale 1 x = x) \<and>
    (\<forall>a x. enorm (scale a x) = knorm a * enorm x)"

definition q944297_isometric_ring_equivalence ::
    "('k::{field,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('l::{field,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'l) \<Rightarrow> ('l \<Rightarrow> 'k) \<Rightarrow> bool" where
  "q944297_isometric_ring_equivalence knorm lnorm sigma sigma_inv \<longleftrightarrow>
    sigma 0 = 0 \<and>
    sigma 1 = 1 \<and>
    (\<forall>a b. sigma (a + b) = sigma a + sigma b) \<and>
    (\<forall>a b. sigma (a * b) = sigma a * sigma b) \<and>
    sigma_inv 0 = 0 \<and>
    sigma_inv 1 = 1 \<and>
    (\<forall>a b. sigma_inv (a + b) = sigma_inv a + sigma_inv b) \<and>
    (\<forall>a b. sigma_inv (a * b) = sigma_inv a * sigma_inv b) \<and>
    (\<forall>a. sigma_inv (sigma a) = a) \<and>
    (\<forall>b. sigma (sigma_inv b) = b) \<and>
    (\<forall>a. lnorm (sigma a) = knorm a) \<and>
    (\<forall>b. knorm (sigma_inv b) = lnorm b)"

definition q944297_continuous_semilinear ::
    "('k \<Rightarrow> 'e::{ab_group_add,metric_space} \<Rightarrow> 'e) \<Rightarrow>
     ('l \<Rightarrow> 'f::{ab_group_add,metric_space} \<Rightarrow> 'f) \<Rightarrow>
     ('k \<Rightarrow> 'l) \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> bool" where
  "q944297_continuous_semilinear escale fscale sigma f \<longleftrightarrow>
    (\<forall>x y. f (x + y) = f x + f y) \<and>
    (\<forall>a x. f (escale a x) = fscale (sigma a) (f x)) \<and>
    continuous_on UNIV f"

theorem open_mapping_theorem:
  fixes knorm :: "'k::{field,metric_space} \<Rightarrow> real"
    and lnorm :: "'l::{field,metric_space} \<Rightarrow> real"
    and enorm :: "'e::{ab_group_add,metric_space,complete_space} \<Rightarrow> real"
    and fnorm :: "'f::{ab_group_add,metric_space,complete_space} \<Rightarrow> real"
    and escale :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and fscale :: "'l \<Rightarrow> 'f \<Rightarrow> 'f"
    and sigma :: "'k \<Rightarrow> 'l"
    and sigma_inv :: "'l \<Rightarrow> 'k"
    and f :: "'e \<Rightarrow> 'f"
  assumes "q944297_nontrivially_normed_field knorm"
    and "q944297_nontrivially_normed_field lnorm"
    and "q944297_normed_space knorm enorm escale"
    and "q944297_normed_space lnorm fnorm fscale"
    and "q944297_isometric_ring_equivalence knorm lnorm sigma sigma_inv"
    and "q944297_continuous_semilinear escale fscale sigma f"
    and "surj f"
  shows "\<forall>S. open S \<longrightarrow> open (f ` S)"
  sorry

end
