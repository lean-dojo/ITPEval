(*
  Statement-only formalization of thousand-theorems corpus artifact Q1050932,
  "Hartogs's theorem": a function from an open subset of complex two-space to
  a separable complex Banach space that is analytic separately in each complex
  coordinate is jointly analytic. This file contains no proof.
*)

theory Q1050932_hartogs_s_theorem
  imports Complex_Main
begin

definition q1050932_complex_banach_structure ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1050932_complex_banach_structure cscale \<longleftrightarrow>
    (\<forall>a x y. cscale a (x + y) = cscale a x + cscale a y) \<and>
    (\<forall>a b x. cscale (a + b) x = cscale a x + cscale b x) \<and>
    (\<forall>a b x. cscale (a * b) x = cscale a (cscale b x)) \<and>
    (\<forall>x. cscale 1 x = x) \<and>
    (\<forall>r x. cscale (of_real r) x = scaleR r x) \<and>
    (\<forall>a x. norm (cscale a x) = norm a * norm x)"

definition q1050932_complex_scale ::
    "complex \<Rightarrow> complex \<Rightarrow> complex" where
  "q1050932_complex_scale a z = a * z"

definition q1050932_complex_add ::
    "complex \<Rightarrow> complex \<Rightarrow> complex" where
  "q1050932_complex_add z w = z + w"

definition q1050932_complex_sub ::
    "complex \<Rightarrow> complex \<Rightarrow> complex" where
  "q1050932_complex_sub z w = z - w"

definition q1050932_complex_norm :: "complex \<Rightarrow> real" where
  "q1050932_complex_norm z = norm z"

definition q1050932_pair_complex_scale ::
    "complex \<Rightarrow> (complex \<times> complex) \<Rightarrow> (complex \<times> complex)" where
  "q1050932_pair_complex_scale a z = (a * fst z, a * snd z)"

definition q1050932_pair_complex_norm ::
    "(complex \<times> complex) \<Rightarrow> real" where
  "q1050932_pair_complex_norm z = max (norm (fst z)) (norm (snd z))"

definition q1050932_pair_complex_add ::
    "(complex \<times> complex) \<Rightarrow> (complex \<times> complex) \<Rightarrow>
      (complex \<times> complex)" where
  "q1050932_pair_complex_add z w =
    (fst z + fst w, snd z + snd w)"

definition q1050932_pair_complex_sub ::
    "(complex \<times> complex) \<Rightarrow> (complex \<times> complex) \<Rightarrow>
      (complex \<times> complex)" where
  "q1050932_pair_complex_sub z w =
    (fst z - fst w, snd z - snd w)"

definition q1050932_open_pair_set ::
    "(complex \<times> complex) set \<Rightarrow> bool" where
  "q1050932_open_pair_set U \<longleftrightarrow>
    (\<forall>z \<in> U. \<exists>r>0. \<forall>w.
      q1050932_pair_complex_norm (q1050932_pair_complex_sub w z) < r
      \<longrightarrow> w \<in> U)"

definition q1050932_continuous_complex_multilinear ::
    "nat \<Rightarrow>
      ('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow>
      (complex \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow>
      ('d \<Rightarrow> real) \<Rightarrow>
      (complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      ('d list \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1050932_continuous_complex_multilinear n dadd dscale dnorm escale A \<longleftrightarrow>
    (\<forall>xs i u v.
      length xs = n \<longrightarrow> i < n \<longrightarrow>
      A (xs[i := dadd u v]) = A (xs[i := u]) + A (xs[i := v])) \<and>
    (\<forall>xs i a u.
      length xs = n \<longrightarrow> i < n \<longrightarrow>
      A (xs[i := dscale a u]) = escale a (A (xs[i := u]))) \<and>
    (\<exists>C\<ge>0. \<forall>xs. length xs = n \<longrightarrow>
      norm (A xs) \<le> C * (\<Prod>i<n. dnorm (xs ! i)))"

definition q1050932_multilinear_operator_norm ::
    "nat \<Rightarrow> ('d \<Rightarrow> real) \<Rightarrow> ('d list \<Rightarrow>
      'e::real_normed_vector) \<Rightarrow> real" where
  "q1050932_multilinear_operator_norm n dnorm A =
    Inf {C. 0 \<le> C \<and> (\<forall>xs. length xs = n \<longrightarrow>
      norm (A xs) \<le> C * (\<Prod>i<n. dnorm (xs ! i)))}"

definition q1050932_analytic_at ::
    "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow>
      ('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow>
      (complex \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow>
      ('d \<Rightarrow> real) \<Rightarrow>
      (complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      ('d \<Rightarrow> 'e) \<Rightarrow> 'd \<Rightarrow> bool" where
  "q1050932_analytic_at dadd dsub dscale dnorm escale g z0 \<longleftrightarrow>
    (\<exists>A r. 0 < r \<and>
      (\<forall>n. q1050932_continuous_complex_multilinear
        n dadd dscale dnorm escale (A n)) \<and>
      summable (\<lambda>n.
        q1050932_multilinear_operator_norm n dnorm (A n) * r ^ n) \<and>
      (\<forall>z. dnorm (dsub z z0) < r \<longrightarrow>
        ((\<lambda>n. A n (replicate n (dsub z z0))) sums g z)))"

definition q1050932_analytic_on_nhd ::
    "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow>
      ('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow>
      (complex \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow>
      ('d \<Rightarrow> real) \<Rightarrow>
      (complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      ('d \<Rightarrow> 'e) \<Rightarrow> 'd set \<Rightarrow> bool" where
  "q1050932_analytic_on_nhd dadd dsub dscale dnorm escale g U \<longleftrightarrow>
    (\<forall>z \<in> U. q1050932_analytic_at
      dadd dsub dscale dnorm escale g z)"

definition q1050932_separable_space ::
    "'e::metric_space itself \<Rightarrow> bool" where
  "q1050932_separable_space _ \<longleftrightarrow>
    (\<exists>d::nat \<Rightarrow> 'e. \<forall>x e. 0 < e \<longrightarrow>
      (\<exists>n. dist x (d n) < e))"

theorem q1050932_hartogs:
  fixes cscale ::
      "complex \<Rightarrow> 'e::banach \<Rightarrow> 'e"
    and f :: "(complex \<times> complex) \<Rightarrow> 'e"
    and U :: "(complex \<times> complex) set"
  assumes complex_banach: "q1050932_complex_banach_structure cscale"
    and separable: "q1050932_separable_space TYPE('e)"
    and open_set: "q1050932_open_pair_set U"
    and analytic_first:
      "\<forall>c0 c1. (c0, c1) \<in> U \<longrightarrow>
        q1050932_analytic_at q1050932_complex_add q1050932_complex_sub
          q1050932_complex_scale q1050932_complex_norm cscale
          (\<lambda>z0. f (z0, c1)) c0"
    and analytic_second:
      "\<forall>c0 c1. (c0, c1) \<in> U \<longrightarrow>
        q1050932_analytic_at q1050932_complex_add q1050932_complex_sub
          q1050932_complex_scale q1050932_complex_norm cscale
          (\<lambda>z1. f (c0, z1)) c1"
  shows
    "q1050932_analytic_on_nhd q1050932_pair_complex_add
      q1050932_pair_complex_sub q1050932_pair_complex_scale
      q1050932_pair_complex_norm cscale f U"
  sorry

end
