(*
  Statement-only formalization of thousand-theorems corpus artifact Q3527217,
  "M. Riesz extension theorem": a real-linear functional on a subspace that
  is nonnegative on its intersection with an additive cone extends to the
  whole real vector space as a linear functional nonnegative on that cone,
  provided the subspace plus the cone covers the space. This file contains
  no proof.
*)

theory Q3527217_m_riesz_extension_theorem
  imports Complex_Main
begin

definition q3527217_real_subspace :: "'a::real_vector set \<Rightarrow> bool" where
  "q3527217_real_subspace p \<longleftrightarrow>
    0 \<in> p \<and>
    (\<forall>x \<in> p. \<forall>y \<in> p. x + y \<in> p) \<and>
    (\<forall>a::real. \<forall>x \<in> p. scaleR a x \<in> p)"

definition q3527217_additive_cone :: "'a::real_vector set \<Rightarrow> bool" where
  "q3527217_additive_cone s \<longleftrightarrow>
    0 \<in> s \<and>
    (\<forall>x \<in> s. \<forall>y \<in> s. x + y \<in> s) \<and>
    (\<forall>a::real. 0 \<le> a \<longrightarrow> (\<forall>x \<in> s. scaleR a x \<in> s))"

definition q3527217_linear_on ::
    "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "q3527217_linear_on p f \<longleftrightarrow>
    (\<forall>x \<in> p. \<forall>y \<in> p. f (x + y) = f x + f y) \<and>
    (\<forall>a::real. \<forall>x \<in> p. f (scaleR a x) = a * f x)"

theorem q3527217_m_riesz_extension:
  fixes p s :: "'a::real_vector set"
    and f :: "'a \<Rightarrow> real"
  assumes subspace: "q3527217_real_subspace p"
    and cone: "q3527217_additive_cone s"
    and linear_on: "q3527217_linear_on p f"
    and nonnegative: "\<forall>x \<in> p. x \<in> s \<longrightarrow> 0 \<le> f x"
    and generating: "\<forall>y. \<exists>x \<in> p. x + y \<in> s"
  shows "\<exists>g :: 'a \<Rightarrow> real.
    q3527217_linear_on UNIV g \<and>
    (\<forall>x \<in> p. g x = f x) \<and>
    (\<forall>x \<in> s. 0 \<le> g x)"
  sorry

end
