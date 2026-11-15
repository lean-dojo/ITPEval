(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q4378868, "Phragmén–Lindelöf theorem": a complex-differentiable,
  complex-normed-space-valued function with controlled double-exponential
  growth and bounded boundary norms is bounded throughout a closed horizontal
  strip. This file contains no proof.
*)

theory Q4378868_phragm_n_lindel_f_theorem
  imports "HOL-Analysis.Complex_Transcendental"
begin

definition q4378868_complex_normed_vector ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q4378868_complex_normed_vector cscale \<longleftrightarrow>
    (\<forall>a x y. cscale a (x + y) = cscale a x + cscale a y) \<and>
    (\<forall>a b x. cscale (a + b) x = cscale a x + cscale b x) \<and>
    (\<forall>a b x. cscale (a * b) x = cscale a (cscale b x)) \<and>
    (\<forall>x. cscale 1 x = x) \<and>
    (\<forall>r x. cscale (of_real r) x = scaleR r x) \<and>
    (\<forall>a x. norm (cscale a x) = norm a * norm x)"

definition q4378868_has_complex_derivative_within ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      (complex \<Rightarrow> 'e) \<Rightarrow> 'e \<Rightarrow> complex set \<Rightarrow>
      complex \<Rightarrow> bool" where
  "q4378868_has_complex_derivative_within cscale f d S z \<longleftrightarrow>
    ((\<lambda>w. cscale (inverse (w - z)) (f w - f z)) \<longlongrightarrow> d)
      (at z within S)"

definition q4378868_horizontal_strip ::
    "real \<Rightarrow> real \<Rightarrow> complex set" where
  "q4378868_horizontal_strip a b = {z. a < Im z \<and> Im z < b}"

definition q4378868_diff_cont_on_cl ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      (complex \<Rightarrow> 'e) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "q4378868_diff_cont_on_cl cscale f a b \<longleftrightarrow>
    (\<forall>z \<in> q4378868_horizontal_strip a b.
      \<exists>d. q4378868_has_complex_derivative_within cscale f d
        (q4378868_horizontal_strip a b) z) \<and>
    continuous_on (closure (q4378868_horizontal_strip a b)) f"

definition q4378868_strip_growth ::
    "(complex \<Rightarrow> 'e::real_normed_vector) \<Rightarrow>
      real \<Rightarrow> real \<Rightarrow> bool" where
  "q4378868_strip_growth f a b \<longleftrightarrow>
    (\<exists>c B A R.
      c < pi / (b - a) \<and> 0 < A \<and>
      (\<forall>w. w \<in> q4378868_horizontal_strip a b \<and> R \<le> abs (Re w)
        \<longrightarrow>
        norm (f w) \<le> A * exp (B * exp (c * abs (Re w)))))"

theorem q4378868_phragmen_lindelof_horizontal_strip:
  fixes cscale :: "complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e"
    and f :: "complex \<Rightarrow> 'e"
    and a b C :: real
    and z :: complex
  assumes complex_space: "q4378868_complex_normed_vector cscale"
    and diff_cont: "q4378868_diff_cont_on_cl cscale f a b"
    and growth: "q4378868_strip_growth f a b"
    and lower_boundary: "\<forall>w. Im w = a \<longrightarrow> norm (f w) \<le> C"
    and upper_boundary: "\<forall>w. Im w = b \<longrightarrow> norm (f w) \<le> C"
    and above_lower: "a \<le> Im z"
    and below_upper: "Im z \<le> b"
  shows "norm (f z) \<le> C"
  sorry

end
