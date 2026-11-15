(*
  Statement-only formalization of the thousand-theorems corpus artifact Q1217677,
  "Fundamental theorem of calculus": strict differentiation of a Banach-space-valued
  indefinite Lebesgue-Bochner integral at an endpoint, and recovery of endpoint
  differences by integrating a right derivative. This file contains no proof.
*)

theory Q1217677_fundamental_theorem_of_calculus
  imports
    "HOL-Analysis.Bochner_Integration"
    "HOL-Analysis.Lebesgue_Measure"
    "HOL-Analysis.Derivative"
begin

definition q1217677_ae_strongly_measurable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> bool" where
  "q1217677_ae_strongly_measurable M f \<longleftrightarrow>
    (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'e.
      (\<forall>n. simple_function M (s n)) \<and>
      (AE x in M. (\<lambda>n. s n x) \<longlonglongrightarrow> f x))"

definition q1217677_strongly_measurable_at ::
    "(real \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> real \<Rightarrow> bool" where
  "q1217677_strongly_measurable_at f b \<longleftrightarrow>
    (\<exists>S. eventually (\<lambda>x. x \<in> S) (nhds b) \<and>
      q1217677_ae_strongly_measurable (restrict_space lborel S) f)"

definition q1217677_has_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> 'e \<Rightarrow> bool" where
  "q1217677_has_bochner_integral M f I \<longleftrightarrow>
    q1217677_ae_strongly_measurable M f \<and>
    (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'e.
      (\<forall>n. Bochner_Integration.simple_bochner_integrable M (s n)) \<and>
      (\<lambda>n. \<integral>\<^sup>+ x. ennreal (norm (f x - s n x)) \<partial>M)
        \<longlonglongrightarrow> 0 \<and>
      (\<lambda>n. Bochner_Integration.simple_bochner_integral M (s n))
        \<longlonglongrightarrow> I)"

definition q1217677_integrable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> bool" where
  "q1217677_integrable M f \<longleftrightarrow>
    (\<exists>I. q1217677_has_bochner_integral M f I)"

definition q1217677_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> 'e" where
  "q1217677_bochner_integral M f =
    (if \<exists>I. q1217677_has_bochner_integral M f I
     then THE I. q1217677_has_bochner_integral M f I
     else 0)"

definition q1217677_interval_integrable ::
    "(real \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "q1217677_interval_integrable f a b \<longleftrightarrow>
    q1217677_integrable (restrict_space lborel {a<..b}) f \<and>
    q1217677_integrable (restrict_space lborel {b<..a}) f"

definition q1217677_interval_integral ::
    "(real \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'e" where
  "q1217677_interval_integral f a b =
    q1217677_bochner_integral (restrict_space lborel {a<..b}) f -
    q1217677_bochner_integral (restrict_space lborel {b<..a}) f"

definition q1217677_has_strict_vector_derivative ::
    "(real \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> bool" where
  "q1217677_has_strict_vector_derivative F c b \<longleftrightarrow>
    (\<forall>e>0. eventually
      (\<lambda>p. norm ((F (fst p) - F (snd p)) -
          (fst p - snd p) *\<^sub>R c)
        \<le> e * norm (fst p - snd p))
      (nhds (b, b)))"

theorem integral_hasStrictDerivAt_of_tendsto_ae_right:
  fixes f :: "real \<Rightarrow> 'e::{real_normed_vector,complete_space}"
    and a b :: real
    and c :: 'e
  assumes interval_integrable:
      "q1217677_interval_integrable f a b"
    and strongly_measurable_at:
      "q1217677_strongly_measurable_at f b"
    and tendsto_ae_right:
      "filterlim f (nhds c) (inf (nhds b) (ae_filter lborel))"
  shows "q1217677_has_strict_vector_derivative
    (\<lambda>u. q1217677_interval_integral f a u) c b"
  sorry

theorem integral_eq_sub_of_hasDeriv_right_of_le:
  fixes f f' :: "real \<Rightarrow> 'e::{real_normed_vector,complete_space}"
    and a b :: real
  assumes le: "a \<le> b"
    and continuous: "continuous_on {a..b} f"
    and right_derivative:
      "\<forall>x \<in> {a<..<b}.
        (f has_vector_derivative f' x) (at x within {x<..})"
    and interval_integrable:
      "q1217677_interval_integrable f' a b"
  shows "q1217677_interval_integral f' a b = f b - f a"
  sorry

end
