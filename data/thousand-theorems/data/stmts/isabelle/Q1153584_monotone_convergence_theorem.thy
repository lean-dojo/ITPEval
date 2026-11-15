(*
  Statement-only formalization of the thousand-theorems corpus artifact Q1153584,
  "Monotone convergence theorem": almost-everywhere monotone convergence for
  extended-nonnegative Lebesgue integrals, together with the antitone
  real-valued Bochner-integral formulation. This file contains no proof.
*)

theory Q1153584_monotone_convergence_theorem
  imports "HOL-Analysis.Complete_Measure"
begin

theorem monotone_convergence_theorem_antitone_real:
  fixes M :: "'a measure"
    and f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and F :: "'a \<Rightarrow> real"
  assumes f_integrable:
      "\<And>n. integrable (completion M) (f n)"
    and F_integrable:
      "integrable (completion M) F"
    and f_antitone:
      "AE x in M. antimono (\<lambda>n. f n x)"
    and f_tendsto:
      "AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> F x"
  shows
      "(\<lambda>n. integral\<^sup>L (completion M) (f n))
        \<longlonglongrightarrow> integral\<^sup>L (completion M) F"
  sorry

theorem monotone_convergence_theorem_nn:
  fixes M :: "'a measure"
    and f :: "nat \<Rightarrow> 'a \<Rightarrow> ennreal"
    and F :: "'a \<Rightarrow> ennreal"
  assumes f_ae_measurable:
      "\<And>n. f n \<in> borel_measurable (completion M)"
    and f_monotone:
      "AE x in M. mono (\<lambda>n. f n x)"
    and f_tendsto:
      "AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> F x"
  shows
      "(\<lambda>n. nn_integral M (f n)) \<longlonglongrightarrow> nn_integral M F"
  sorry

end
