(*
  Statement-only formalization of thousand-theorems corpus artifact Q1038716,
  "Identity theorem": two functions from an arbitrary nontrivially normed field
  to a normed vector space, analytic on neighborhoods of a preconnected set and
  agreeing frequently in a punctured neighborhood of a point of that set,
  agree throughout the set. This file contains no proof.
*)

theory Q1038716_identity_theorem
  imports Complex_Main
begin

definition q1038716_nontrivially_normed_field ::
    "('k::{field,metric_space} \<Rightarrow> real) \<Rightarrow> bool" where
  "q1038716_nontrivially_normed_field knorm \<longleftrightarrow>
    knorm 0 = 0 \<and>
    (\<forall>a. 0 \<le> knorm a) \<and>
    (\<forall>a. knorm a = 0 \<longleftrightarrow> a = 0) \<and>
    (\<forall>a. knorm (-a) = knorm a) \<and>
    (\<forall>a b. knorm (a + b) \<le> knorm a + knorm b) \<and>
    (\<forall>a b. knorm (a * b) = knorm a * knorm b) \<and>
    (\<forall>a b. dist a b = knorm (a - b)) \<and>
    (\<exists>a. 1 < knorm a)"

definition q1038716_normed_space ::
    "('k::{field,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('e::{ab_group_add,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1038716_normed_space knorm enorm scale \<longleftrightarrow>
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
    (\<forall>a x. enorm (scale a x) \<le> knorm a * enorm x)"

definition q1038716_continuous_multilinear ::
    "nat \<Rightarrow>
     ('k::{field,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('e::{ab_group_add,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
     ('k list \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1038716_continuous_multilinear n knorm enorm scale A \<longleftrightarrow>
    (\<forall>xs i u v.
      length xs = n \<longrightarrow> i < n \<longrightarrow>
      A (xs[i := u + v]) = A (xs[i := u]) + A (xs[i := v])) \<and>
    (\<forall>xs i a u.
      length xs = n \<longrightarrow> i < n \<longrightarrow>
      A (xs[i := a * u]) = scale a (A (xs[i := u]))) \<and>
    (\<exists>C\<ge>0. \<forall>xs. length xs = n \<longrightarrow>
      enorm (A xs) \<le> C * (\<Prod>i<n. knorm (xs ! i)))"

definition q1038716_multilinear_operator_norm ::
    "nat \<Rightarrow>
     ('k::{field,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('e::{ab_group_add,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('k list \<Rightarrow> 'e) \<Rightarrow> real" where
  "q1038716_multilinear_operator_norm n knorm enorm A =
    Inf {C. 0 \<le> C \<and> (\<forall>xs. length xs = n \<longrightarrow>
      enorm (A xs) \<le> C * (\<Prod>i<n. knorm (xs ! i)))}"

definition q1038716_analytic_at ::
    "('k::{field,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('e::{ab_group_add,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
     ('k \<Rightarrow> 'e) \<Rightarrow> 'k \<Rightarrow> bool" where
  "q1038716_analytic_at knorm enorm scale f z0 \<longleftrightarrow>
    (\<exists>A r. 0 < r \<and>
      (\<forall>n. q1038716_continuous_multilinear
        n knorm enorm scale (A n)) \<and>
      summable (\<lambda>n.
        q1038716_multilinear_operator_norm n knorm enorm (A n) * r ^ n) \<and>
      (\<forall>z. dist z z0 < r \<longrightarrow>
        ((\<lambda>n. A n (replicate n (z - z0))) sums f z)))"

definition q1038716_analytic_on_nhd ::
    "('k::{field,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('e::{ab_group_add,metric_space} \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
     ('k \<Rightarrow> 'e) \<Rightarrow> 'k set \<Rightarrow> bool" where
  "q1038716_analytic_on_nhd knorm enorm scale f U \<longleftrightarrow>
    (\<forall>z \<in> U. q1038716_analytic_at knorm enorm scale f z)"

theorem identity_theorem:
  fixes knorm :: "'k::{field,metric_space} \<Rightarrow> real"
    and enorm :: "'e::{ab_group_add,metric_space} \<Rightarrow> real"
    and scale :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and U :: "'k set"
    and f g :: "'k \<Rightarrow> 'e"
    and z0 :: 'k
  assumes "q1038716_nontrivially_normed_field knorm"
    and "q1038716_normed_space knorm enorm scale"
    and "q1038716_analytic_on_nhd knorm enorm scale f U"
    and "q1038716_analytic_on_nhd knorm enorm scale g U"
    and "connected U"
    and "z0 \<in> U"
    and "frequently (\<lambda>z. f z = g z) (at z0)"
  shows "\<forall>z \<in> U. f z = g z"
  sorry

end
