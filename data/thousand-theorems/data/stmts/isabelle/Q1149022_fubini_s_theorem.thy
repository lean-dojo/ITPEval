(*
  Statement-only formalization of thousand-theorems corpus artifact Q1149022,
  "Fubini's theorem": the Bochner integral of an integrable real normed-space-
  valued function over a product of s-finite measure spaces equals its iterated
  Bochner integral. This file contains no proof.
*)

theory Q1149022_fubini_s_theorem
  imports "HOL-Analysis.Bochner_Integration"
begin

definition q1149022_s_finite_measure :: "'a measure \<Rightarrow> bool" where
  "q1149022_s_finite_measure M \<longleftrightarrow>
    (\<exists>Ms :: nat \<Rightarrow> 'a measure.
      (\<forall>n. sets (Ms n) = sets M) \<and>
      (\<forall>n. emeasure (Ms n) (space M) < \<infinity>) \<and>
      (\<forall>A. emeasure M A = (\<Sum>n. emeasure (Ms n) A)))"

definition q1149022_ae_strongly_measurable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool" where
  "q1149022_ae_strongly_measurable M f \<longleftrightarrow>
    (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'b.
      (\<forall>n. simple_function M (s n)) \<and>
      (AE x in M. (\<lambda>n. s n x) \<longlonglongrightarrow> f x))"

definition q1149022_integrable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool" where
  "q1149022_integrable M f \<longleftrightarrow>
    q1149022_ae_strongly_measurable M f \<and>
    (\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>M) < \<infinity>"

definition q1149022_has_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> bool" where
  "q1149022_has_bochner_integral M f I \<longleftrightarrow>
    q1149022_ae_strongly_measurable M f \<and>
    (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'b.
      (\<forall>n. Bochner_Integration.simple_bochner_integrable M (s n)) \<and>
      (\<lambda>n. \<integral>\<^sup>+ x. ennreal (norm (f x - s n x)) \<partial>M)
        \<longlonglongrightarrow> 0 \<and>
      (\<lambda>n. Bochner_Integration.simple_bochner_integral M (s n))
        \<longlonglongrightarrow> I)"

definition q1149022_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b" where
  "q1149022_bochner_integral M f =
    (if complete (UNIV :: 'b set) then
      if \<exists>I. q1149022_has_bochner_integral M f I
      then THE I. q1149022_has_bochner_integral M f I
      else 0
    else 0)"

theorem fubini_s_theorem:
  fixes M :: "'a measure"
    and N :: "'b measure"
    and f :: "'a \<times> 'b \<Rightarrow> 'c::real_normed_vector"
  assumes "q1149022_s_finite_measure M"
    and "q1149022_s_finite_measure N"
    and "q1149022_integrable (M \<Otimes>\<^sub>M N) f"
  shows "q1149022_bochner_integral (M \<Otimes>\<^sub>M N) f =
    q1149022_bochner_integral M
      (\<lambda>x. q1149022_bochner_integral N (\<lambda>y. f (x, y)))"
  sorry

end
