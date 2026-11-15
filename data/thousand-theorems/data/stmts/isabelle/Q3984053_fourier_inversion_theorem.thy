(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q3984053 (thousand-theorems__isabelle__Q3984053), "Fourier inversion theorem":
  the inverse Fourier transform of the Fourier transform of a continuous
  integrable function on a finite-dimensional real inner product space is the
  original function when its Fourier transform is also integrable. This file
  contains no proof.
*)

theory Q3984053_fourier_inversion_theorem
  imports "HOL-Analysis.Bochner_Integration" "HOL-Analysis.Lebesgue_Measure"
begin

definition q3984053_complex_normed_vector ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q3984053_complex_normed_vector cscale \<longleftrightarrow>
    (\<forall>a x y. cscale a (x + y) = cscale a x + cscale a y) \<and>
    (\<forall>a b x. cscale (a + b) x = cscale a x + cscale b x) \<and>
    (\<forall>a b x. cscale (a * b) x = cscale a (cscale b x)) \<and>
    (\<forall>x. cscale 1 x = x) \<and>
    (\<forall>r x. cscale (of_real r) x = scaleR r x) \<and>
    (\<forall>a x. norm (cscale a x) = norm a * norm x)"

definition q3984053_orthonormal_basis ::
    "'v::real_inner set \<Rightarrow> bool" where
  "q3984053_orthonormal_basis B \<longleftrightarrow>
    finite_dimensional_vector_space
      ((*\<^sub>R) :: real \<Rightarrow> 'v \<Rightarrow> 'v) B \<and>
    (\<forall>u \<in> B. \<forall>v \<in> B. inner u v = (if u = v then 1 else 0))"

definition q3984053_parallelotope ::
    "'v::real_vector set \<Rightarrow> 'v set" where
  "q3984053_parallelotope B =
    {(\<Sum>b\<in>B. c b *\<^sub>R b) | c. \<forall>b \<in> B. 0 \<le> c b \<and> c b < 1}"

definition q3984053_lebesgue_measure ::
    "'v::real_inner measure \<Rightarrow> bool" where
  "q3984053_lebesgue_measure M \<longleftrightarrow>
    sets M = sets borel \<and>
    (\<forall>a. distr M borel ((+) a) = M) \<and>
    (\<forall>B. q3984053_orthonormal_basis B \<longrightarrow>
      measure M (q3984053_parallelotope B) = 1)"

definition q3984053_ae_strongly_measurable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> bool" where
  "q3984053_ae_strongly_measurable M f \<longleftrightarrow>
    (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'e.
      (\<forall>n. simple_function M (s n)) \<and>
      (AE x in M. (\<lambda>n. s n x) \<longlonglongrightarrow> f x))"

definition q3984053_has_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> 'e \<Rightarrow> bool" where
  "q3984053_has_bochner_integral M f I \<longleftrightarrow>
    q3984053_ae_strongly_measurable M f \<and>
    (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'e.
      (\<forall>n. Bochner_Integration.simple_bochner_integrable M (s n)) \<and>
      ((\<lambda>n. \<integral>\<^sup>+x. ennreal (norm (f x - s n x)) \<partial>M)
        \<longlonglongrightarrow> 0) \<and>
      ((\<lambda>n. Bochner_Integration.simple_bochner_integral M (s n))
        \<longlonglongrightarrow> I))"

definition q3984053_integrable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> bool" where
  "q3984053_integrable M f \<longleftrightarrow>
    q3984053_ae_strongly_measurable M f \<and>
    (\<integral>\<^sup>+x. ennreal (norm (f x)) \<partial>M) < \<infinity>"

definition q3984053_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> 'e" where
  "q3984053_bochner_integral M f =
    (if \<exists>I. q3984053_has_bochner_integral M f I
     then THE I. q3984053_has_bochner_integral M f I
     else 0)"

definition q3984053_fourier ::
    "'v::real_inner measure \<Rightarrow>
      (complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      ('v \<Rightarrow> 'e) \<Rightarrow> 'v \<Rightarrow> 'e" where
  "q3984053_fourier M cscale f w =
    q3984053_bochner_integral M
      (\<lambda>x. cscale (exp (- (\<i> * of_real (2 * pi * inner w x)))) (f x))"

definition q3984053_fourier_inverse ::
    "'v::real_inner measure \<Rightarrow>
      (complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      ('v \<Rightarrow> 'e) \<Rightarrow> 'v \<Rightarrow> 'e" where
  "q3984053_fourier_inverse M cscale f v =
    q3984053_bochner_integral M
      (\<lambda>w. cscale (exp (\<i> * of_real (2 * pi * inner w v))) (f w))"

theorem continuous_fourier_inversion:
  fixes M :: "'v::real_inner measure"
    and cscale :: "complex \<Rightarrow> 'e::{real_normed_vector,complete_space} \<Rightarrow> 'e"
    and f :: "'v \<Rightarrow> 'e"
  assumes finite_dimensional:
      "\<exists>B. q3984053_orthonormal_basis B"
    and lebesgue_measure: "q3984053_lebesgue_measure M"
    and complex_space: "q3984053_complex_normed_vector cscale"
    and continuous: "continuous_on UNIV f"
    and f_integrable: "q3984053_integrable M f"
    and fourier_integrable:
      "q3984053_integrable M (q3984053_fourier M cscale f)"
  shows
    "q3984053_fourier_inverse M cscale (q3984053_fourier M cscale f) = f"
  sorry

end
