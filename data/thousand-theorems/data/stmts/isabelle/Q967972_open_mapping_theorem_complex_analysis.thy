(*
  Statement-only formalization of thousand-theorems corpus artifact Q967972,
  "Open mapping theorem (complex analysis)": an analytic complex-valued
  function on a preconnected subset of an arbitrary complex normed vector
  space is either constant there or maps every open subset to an open set.
  This file contains no proof.
*)

theory Q967972_open_mapping_theorem_complex_analysis
  imports "HOL-Analysis.Complex_Analysis_Basics"
begin

definition q967972_complex_normed_vector ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q967972_complex_normed_vector cscale \<longleftrightarrow>
    (\<forall>a x y. cscale a (x + y) = cscale a x + cscale a y) \<and>
    (\<forall>a b x. cscale (a + b) x = cscale a x + cscale b x) \<and>
    (\<forall>a b x. cscale (a * b) x = cscale a (cscale b x)) \<and>
    (\<forall>x. cscale 1 x = x) \<and>
    (\<forall>r x. cscale (of_real r) x = scaleR r x) \<and>
    (\<forall>a x. norm (cscale a x) = norm a * norm x)"

definition q967972_continuous_complex_multilinear ::
    "nat \<Rightarrow>
      (complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      ('e list \<Rightarrow> complex) \<Rightarrow> bool" where
  "q967972_continuous_complex_multilinear k cscale A \<longleftrightarrow>
    (\<forall>xs i u v.
      length xs = k \<longrightarrow> i < k \<longrightarrow>
      A (xs[i := u + v]) = A (xs[i := u]) + A (xs[i := v])) \<and>
    (\<forall>xs i a u.
      length xs = k \<longrightarrow> i < k \<longrightarrow>
      A (xs[i := cscale a u]) = a * A (xs[i := u])) \<and>
    (\<exists>C\<ge>0. \<forall>xs. length xs = k \<longrightarrow>
      norm (A xs) \<le> C * (\<Prod>i<k. norm (xs ! i)))"

definition q967972_multilinear_operator_norm ::
    "nat \<Rightarrow> ('e::real_normed_vector list \<Rightarrow> complex) \<Rightarrow> real" where
  "q967972_multilinear_operator_norm k A =
    Inf {C. 0 \<le> C \<and> (\<forall>xs. length xs = k \<longrightarrow>
      norm (A xs) \<le> C * (\<Prod>i<k. norm (xs ! i)))}"

definition q967972_analytic_at ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      ('e \<Rightarrow> complex) \<Rightarrow> 'e \<Rightarrow> bool" where
  "q967972_analytic_at cscale g z0 \<longleftrightarrow>
    (\<exists>A r. 0 < r \<and>
      (\<forall>n. q967972_continuous_complex_multilinear n cscale (A n)) \<and>
      summable (\<lambda>n.
        q967972_multilinear_operator_norm n (A n) * r ^ n) \<and>
      (\<forall>z. dist z z0 < r \<longrightarrow>
        ((\<lambda>n. A n (replicate n (z - z0))) sums g z)))"

definition q967972_analytic_on_nhd ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      ('e \<Rightarrow> complex) \<Rightarrow> 'e set \<Rightarrow> bool" where
  "q967972_analytic_on_nhd cscale g U \<longleftrightarrow>
    (\<forall>z \<in> U. q967972_analytic_at cscale g z)"

theorem q967972_open_mapping_theorem:
  fixes cscale :: "complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e"
    and g :: "'e \<Rightarrow> complex"
    and U :: "'e set"
  assumes complex_space: "q967972_complex_normed_vector cscale"
    and analytic: "q967972_analytic_on_nhd cscale g U"
    and preconnected: "connected U"
  shows "(\<exists>w. \<forall>z \<in> U. g z = w) \<or>
    (\<forall>s. s \<subseteq> U \<longrightarrow> open s \<longrightarrow> open (g ` s))"
  sorry

end
