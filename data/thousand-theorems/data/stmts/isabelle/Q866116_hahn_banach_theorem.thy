(*
  Statement-only formalization of thousand-theorems corpus artifact Q866116,
  "Hahn–Banach theorem": a continuous linear functional on a subspace of a
  seminormed space over a real-or-complex normed field extends to the whole
  space without changing its operator norm. This file contains no proof.
*)

theory Q866116_hahn_banach_theorem
  imports Complex_Main
begin

definition q866116_is_RCLike_normed_field ::
    "('k::field \<Rightarrow> real) \<Rightarrow> bool" where
  "q866116_is_RCLike_normed_field knorm \<longleftrightarrow>
    (\<exists>to_real :: 'k \<Rightarrow> real.
      bij to_real \<and>
      to_real 0 = 0 \<and>
      to_real 1 = 1 \<and>
      (\<forall>a b. to_real (a + b) = to_real a + to_real b) \<and>
      (\<forall>a b. to_real (a * b) = to_real a * to_real b) \<and>
      (\<forall>a. knorm a = abs (to_real a))) \<or>
    (\<exists>to_complex :: 'k \<Rightarrow> complex.
      bij to_complex \<and>
      to_complex 0 = 0 \<and>
      to_complex 1 = 1 \<and>
      (\<forall>a b. to_complex (a + b) = to_complex a + to_complex b) \<and>
      (\<forall>a b. to_complex (a * b) = to_complex a * to_complex b) \<and>
      (\<forall>a. knorm a = norm (to_complex a)))"

definition q866116_seminormed_space ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
     ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q866116_seminormed_space knorm enorm scale \<longleftrightarrow>
    enorm 0 = 0 \<and>
    (\<forall>x. 0 \<le> enorm x) \<and>
    (\<forall>x. enorm (-x) = enorm x) \<and>
    (\<forall>x y. enorm (x + y) \<le> enorm x + enorm y) \<and>
    (\<forall>a x y. scale a (x + y) = scale a x + scale a y) \<and>
    (\<forall>a b x. scale (a + b) x = scale a x + scale b x) \<and>
    (\<forall>a b x. scale (a * b) x = scale a (scale b x)) \<and>
    (\<forall>x. scale 1 x = x) \<and>
    (\<forall>a x. enorm (scale a x) = knorm a * enorm x)"

definition q866116_subspace ::
    "('k::field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
     'e set \<Rightarrow> bool" where
  "q866116_subspace scale p \<longleftrightarrow>
    0 \<in> p \<and>
    (\<forall>x \<in> p. \<forall>y \<in> p. x + y \<in> p) \<and>
    (\<forall>a x. x \<in> p \<longrightarrow> scale a x \<in> p)"

definition q866116_continuous_linear_on ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
     ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
     'e set \<Rightarrow> ('e \<Rightarrow> 'k) \<Rightarrow> bool" where
  "q866116_continuous_linear_on knorm enorm scale p f \<longleftrightarrow>
    (\<forall>x \<in> p. \<forall>y \<in> p. f (x + y) = f x + f y) \<and>
    (\<forall>a x. x \<in> p \<longrightarrow> f (scale a x) = a * f x) \<and>
    (\<exists>C \<ge> 0. \<forall>x \<in> p. knorm (f x) \<le> C * enorm x)"

definition q866116_operator_norm_on ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
     ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
     'e set \<Rightarrow> ('e \<Rightarrow> 'k) \<Rightarrow> real" where
  "q866116_operator_norm_on knorm enorm p f =
    Inf {C. 0 \<le> C \<and> (\<forall>x \<in> p. knorm (f x) \<le> C * enorm x)}"

theorem exists_extension_norm_eq:
  fixes knorm :: "'k::field \<Rightarrow> real"
    and enorm :: "'e::ab_group_add \<Rightarrow> real"
    and scale :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and p :: "'e set"
    and f :: "'e \<Rightarrow> 'k"
  assumes "q866116_is_RCLike_normed_field knorm"
    and "q866116_seminormed_space knorm enorm scale"
    and "q866116_subspace scale p"
    and "q866116_continuous_linear_on knorm enorm scale p f"
  shows "\<exists>g :: 'e \<Rightarrow> 'k.
    q866116_continuous_linear_on knorm enorm scale UNIV g \<and>
    (\<forall>x \<in> p. g x = f x) \<and>
    q866116_operator_norm_on knorm enorm UNIV g =
      q866116_operator_norm_on knorm enorm p f"
  sorry

end
