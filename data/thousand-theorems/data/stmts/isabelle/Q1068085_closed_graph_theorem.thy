(*
  Statement-only formalization of thousand-theorems corpus artifact Q1068085,
  "Closed graph theorem": a linear map between Banach spaces over an arbitrary
  nontrivially normed field is continuous when its graph is closed. This file
  contains no proof.
*)

theory Q1068085_closed_graph_theorem
  imports Complex_Main
begin

definition q1068085_nontrivially_normed_field_structure ::
    "('k::{field,metric_space} \<Rightarrow> real) \<Rightarrow> bool" where
  "q1068085_nontrivially_normed_field_structure knorm \<longleftrightarrow>
    (\<forall>x. 0 \<le> knorm x) \<and>
    (\<forall>x. knorm x = 0 \<longleftrightarrow> x = 0) \<and>
    (\<forall>x y. knorm (x + y) \<le> knorm x + knorm y) \<and>
    (\<forall>x y. knorm (x * y) = knorm x * knorm y) \<and>
    (\<forall>x y. dist x y = knorm (x - y)) \<and>
    (\<exists>x. 1 < knorm x)"

definition q1068085_normed_space_structure ::
    "('k::{field,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('e::{ab_group_add,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1068085_normed_space_structure knorm enorm scale \<longleftrightarrow>
    (\<forall>x. 0 \<le> enorm x) \<and>
    (\<forall>x. enorm x = 0 \<longleftrightarrow> x = 0) \<and>
    (\<forall>x y. enorm (x + y) \<le> enorm x + enorm y) \<and>
    (\<forall>x y. dist x y = enorm (x - y)) \<and>
    (\<forall>c x y. scale c (x + y) = scale c x + scale c y) \<and>
    (\<forall>c d x. scale (c + d) x = scale c x + scale d x) \<and>
    (\<forall>c d x. scale c (scale d x) = scale (c * d) x) \<and>
    (\<forall>x. scale 1 x = x) \<and>
    (\<forall>c x. enorm (scale c x) \<le> knorm c * enorm x)"

definition q1068085_linear_map ::
    "('k \<Rightarrow> 'e::{ab_group_add,metric_space} \<Rightarrow> 'e) \<Rightarrow>
     ('k \<Rightarrow> 'f::{ab_group_add,metric_space} \<Rightarrow> 'f) \<Rightarrow>
     ('e \<Rightarrow> 'f) \<Rightarrow> bool" where
  "q1068085_linear_map escale fscale g \<longleftrightarrow>
    (\<forall>x y. g (x + y) = g x + g y) \<and>
    (\<forall>c x. g (escale c x) = fscale c (g x))"

theorem closed_graph_theorem:
  fixes knorm :: "'k::{field,metric_space} \<Rightarrow> real"
    and enorm :: "'e::{ab_group_add,metric_space,complete_space} \<Rightarrow> real"
    and fnorm :: "'f::{ab_group_add,metric_space,complete_space} \<Rightarrow> real"
    and escale :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and fscale :: "'k \<Rightarrow> 'f \<Rightarrow> 'f"
    and g :: "'e \<Rightarrow> 'f"
  assumes "q1068085_nontrivially_normed_field_structure knorm"
    and "q1068085_normed_space_structure knorm enorm escale"
    and "q1068085_normed_space_structure knorm fnorm fscale"
    and "q1068085_linear_map escale fscale g"
    and "closed {(x, y). y = g x}"
  shows "continuous_on UNIV g"
  sorry

end
