(*
  Statement-only formalization of the thousand-theorems corpus artifact Q1067156,
  "Dominated convergence theorem": almost-everywhere pointwise convergence of
  strongly measurable vector-valued functions dominated in norm by an integrable
  real function implies convergence of their Bochner integrals.
  This file contains no proof.
*)

theory Q1067156_dominated_convergence_theorem
  imports "HOL-Analysis.Bochner_Integration"
begin

definition q1067156_ae_strongly_measurable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool"
  where
    "q1067156_ae_strongly_measurable M g \<longleftrightarrow>
      (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'b.
        (\<forall>n. simple_function M (s n)) \<and>
        (AE x in M. (\<lambda>n. s n x) \<longlonglongrightarrow> g x))"

definition q1067156_integrable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool"
  where
    "q1067156_integrable M g \<longleftrightarrow>
      q1067156_ae_strongly_measurable M g \<and>
      (\<integral>\<^sup>+ x. ennreal (norm (g x)) \<partial>M) < \<infinity>"

definition q1067156_has_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> bool"
  where
    "q1067156_has_bochner_integral M g I \<longleftrightarrow>
      q1067156_ae_strongly_measurable M g \<and>
      (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'b.
        (\<forall>n. Bochner_Integration.simple_bochner_integrable M (s n)) \<and>
        (\<lambda>n. \<integral>\<^sup>+ x. ennreal (norm (g x - s n x)) \<partial>M)
          \<longlonglongrightarrow> 0 \<and>
        (\<lambda>n. Bochner_Integration.simple_bochner_integral M (s n))
          \<longlonglongrightarrow> I)"

definition q1067156_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b"
  where
    "q1067156_bochner_integral M g =
      (if complete (UNIV :: 'b set) then
        if \<exists>I. q1067156_has_bochner_integral M g I
        then THE I. q1067156_has_bochner_integral M g I
        else 0
      else 0)"

theorem dominated_convergence_theorem:
  fixes M :: "'a measure"
    and F :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::real_normed_vector"
    and f :: "'a \<Rightarrow> 'b"
    and bound :: "'a \<Rightarrow> real"
  assumes F_measurable:
      "\<And>n. q1067156_ae_strongly_measurable M (F n)"
    and bound_integrable:
      "q1067156_integrable M bound"
    and h_bound:
      "\<And>n. AE a in M. norm (F n a) \<le> bound a"
    and h_lim:
      "AE a in M. (\<lambda>n. F n a) \<longlonglongrightarrow> f a"
  shows
      "(\<lambda>n. q1067156_bochner_integral M (F n))
        \<longlonglongrightarrow> q1067156_bochner_integral M f"
  sorry

end
