(*
  Statement-only formalization of the Thousand Theorems artifact Q1067156X,
  "Bounded convergence theorem". This uses Isabelle's native finite-measure,
  almost-everywhere, filter, bounded-continuous-function, ennreal, and
  nonnegative-Lebesgue-integral infrastructure. This file contains no proof.
*)

theory Q1067156X_bounded_convergence_theorem
  imports
    "HOL-Analysis.Complete_Measure"
    "HOL-Analysis.Bounded_Continuous_Function"
    "HOL-Analysis.Infinite_Sum"
begin

theorem bounded_convergence_filter:
  fixes M :: "'a::topological_space measure"
    and L :: "'i filter"
    and fs :: "'i \<Rightarrow> ('a \<Rightarrow>\<^sub>C real)"
    and c :: real
    and f :: "'a \<Rightarrow> real"
  assumes finite_measure: "finite_measure M"
    and opens_measurable: "sets borel \<subseteq> sets M"
    and countably_generated: "countably_generated_filter L"
    and c_nonnegative: "0 \<le> c"
    and fs_nonnegative: "\<And>i x. 0 \<le> fs i x"
    and f_nonnegative: "\<And>x. 0 \<le> f x"
    and fs_le_const: "\<forall>\<^sub>F i in L. AE x in M. fs i x \<le> c"
    and fs_lim: "AE x in M. ((\<lambda>i. fs i x) \<longlongrightarrow> f x) L"
  shows
    "((\<lambda>i. \<integral>\<^sup>+x. ennreal (fs i x) \<partial>M) \<longlongrightarrow>
      (\<integral>\<^sup>+x. ennreal (f x) \<partial>M)) L"
  sorry

theorem bounded_convergence_theorem:
  fixes M :: "'a::topological_space measure"
    and fs :: "nat \<Rightarrow> ('a \<Rightarrow>\<^sub>C real)"
    and c :: real
    and f :: "'a \<Rightarrow> real"
  assumes finite_measure: "finite_measure M"
    and opens_measurable: "sets borel \<subseteq> sets M"
    and c_nonnegative: "0 \<le> c"
    and fs_nonnegative: "\<And>n x. 0 \<le> fs n x"
    and f_nonnegative: "\<And>x. 0 \<le> f x"
    and fs_le_const: "\<And>n x. fs n x \<le> c"
    and fs_lim: "\<And>x. (\<lambda>n. fs n x) \<longlonglongrightarrow> f x"
  shows
    "(\<lambda>n. \<integral>\<^sup>+x. ennreal (fs n x) \<partial>M) \<longlonglongrightarrow>
      (\<integral>\<^sup>+x. ennreal (f x) \<partial>M)"
  sorry

end
