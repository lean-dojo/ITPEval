(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q179467 (thousand-theorems__isabelle__Q179467), "Fourier theorem": Fourier
  inversion for integrable functions from a finite-dimensional real
  inner-product space to a complete complex normed space, pointwise at
  continuity points and globally for continuous functions. This file contains
  no proof.
*)

theory Q179467_fourier_theorem
  imports "HOL-Analysis.Bochner_Integration" "HOL-Analysis.Lebesgue_Measure"
begin

definition q179467_complex_normed_vector ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q179467_complex_normed_vector cscale \<longleftrightarrow>
    (\<forall>a x y. cscale a (x + y) = cscale a x + cscale a y) \<and>
    (\<forall>a b x. cscale (a + b) x = cscale a x + cscale b x) \<and>
    (\<forall>a b x. cscale (a * b) x = cscale a (cscale b x)) \<and>
    (\<forall>x. cscale 1 x = x) \<and>
    (\<forall>r x. cscale (of_real r) x = scaleR r x) \<and>
    (\<forall>a x. norm (cscale a x) = norm a * norm x)"

definition q179467_orthonormal_basis ::
    "'v::real_inner set \<Rightarrow> bool" where
  "q179467_orthonormal_basis B \<longleftrightarrow>
    finite_dimensional_vector_space
      ((*\<^sub>R) :: real \<Rightarrow> 'v \<Rightarrow> 'v) B \<and>
    (\<forall>u \<in> B. \<forall>v \<in> B. inner u v = (if u = v then 1 else 0))"

definition q179467_parallelotope ::
    "'v::real_vector set \<Rightarrow> 'v set" where
  "q179467_parallelotope B =
    {(\<Sum>b\<in>B. c b *\<^sub>R b) | c. \<forall>b \<in> B. 0 \<le> c b \<and> c b < 1}"

definition q179467_lebesgue_measure ::
    "'v::real_inner measure \<Rightarrow> bool" where
  "q179467_lebesgue_measure M \<longleftrightarrow>
    sets M = sets borel \<and>
    (\<forall>a. distr M borel ((+) a) = M) \<and>
    (\<forall>B. q179467_orthonormal_basis B \<longrightarrow>
      measure M (q179467_parallelotope B) = 1)"

definition q179467_ae_strongly_measurable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> bool" where
  "q179467_ae_strongly_measurable M f \<longleftrightarrow>
    (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'e.
      (\<forall>n. simple_function M (s n)) \<and>
      (AE x in M. (\<lambda>n. s n x) \<longlonglongrightarrow> f x))"

definition q179467_has_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> 'e \<Rightarrow> bool" where
  "q179467_has_bochner_integral M f I \<longleftrightarrow>
    q179467_ae_strongly_measurable M f \<and>
    (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'e.
      (\<forall>n. Bochner_Integration.simple_bochner_integrable M (s n)) \<and>
      ((\<lambda>n. \<integral>\<^sup>+x. ennreal (norm (f x - s n x)) \<partial>M)
        \<longlonglongrightarrow> 0) \<and>
      ((\<lambda>n. Bochner_Integration.simple_bochner_integral M (s n))
        \<longlonglongrightarrow> I))"

definition q179467_integrable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> bool" where
  "q179467_integrable M f \<longleftrightarrow>
    (\<exists>I. q179467_has_bochner_integral M f I)"

definition q179467_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> 'e" where
  "q179467_bochner_integral M f =
    (if \<exists>I. q179467_has_bochner_integral M f I
     then THE I. q179467_has_bochner_integral M f I
     else 0)"

definition q179467_fourier ::
    "'v::real_inner measure \<Rightarrow>
      (complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      ('v \<Rightarrow> 'e) \<Rightarrow> 'v \<Rightarrow> 'e" where
  "q179467_fourier M cscale f w =
    q179467_bochner_integral M
      (\<lambda>x. cscale (exp (- (\<i> * of_real (2 * pi * inner w x)))) (f x))"

definition q179467_fourier_inverse ::
    "'v::real_inner measure \<Rightarrow>
      (complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      ('v \<Rightarrow> 'e) \<Rightarrow> 'v \<Rightarrow> 'e" where
  "q179467_fourier_inverse M cscale f v =
    q179467_bochner_integral M
      (\<lambda>w. cscale (exp (\<i> * of_real (2 * pi * inner w v))) (f w))"

theorem fourier_inversion_at_continuity_point:
  fixes M :: "'v::real_inner measure"
    and cscale :: "complex \<Rightarrow> 'e::{real_normed_vector,complete_space} \<Rightarrow> 'e"
    and f :: "'v \<Rightarrow> 'e"
    and v :: 'v
  assumes finite_dimensional:
      "\<exists>B. q179467_orthonormal_basis B"
    and lebesgue_measure: "q179467_lebesgue_measure M"
    and complex_space: "q179467_complex_normed_vector cscale"
    and f_integrable: "q179467_integrable M f"
    and fourier_integrable:
      "q179467_integrable M (q179467_fourier M cscale f)"
    and continuous_at: "continuous (at v) f"
  shows
    "q179467_fourier_inverse M cscale (q179467_fourier M cscale f) v = f v"
  sorry

theorem continuous_fourier_inversion:
  fixes M :: "'v::real_inner measure"
    and cscale :: "complex \<Rightarrow> 'e::{real_normed_vector,complete_space} \<Rightarrow> 'e"
    and f :: "'v \<Rightarrow> 'e"
  assumes finite_dimensional:
      "\<exists>B. q179467_orthonormal_basis B"
    and lebesgue_measure: "q179467_lebesgue_measure M"
    and complex_space: "q179467_complex_normed_vector cscale"
    and continuous: "continuous_on UNIV f"
    and f_integrable: "q179467_integrable M f"
    and fourier_integrable:
      "q179467_integrable M (q179467_fourier M cscale f)"
  shows
    "q179467_fourier_inverse M cscale (q179467_fourier M cscale f) = f"
  sorry

end
