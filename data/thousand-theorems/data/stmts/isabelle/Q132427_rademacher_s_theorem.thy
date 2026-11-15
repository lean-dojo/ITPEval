(*
  Statement-only formalization of the thousand-theorems corpus artifact Q132427,
  "Rademacher's theorem": a Lipschitz map on a measurable subset of an arbitrary
  finite-dimensional real normed vector space into another such space is
  Frechet differentiable within the subset almost everywhere with respect to
  the additive Haar measure restricted to that subset. This file contains no
  proof.
*)

theory Q132427_rademacher_s_theorem
  imports "HOL-Analysis.Lipschitz" "HOL-Analysis.Bochner_Integration"
begin

definition q132427_additive_haar_measure ::
    "'e::real_normed_vector measure \<Rightarrow> bool" where
  "q132427_additive_haar_measure M \<longleftrightarrow>
    sets M = sets borel \<and>
    (\<forall>K. compact K \<longrightarrow> emeasure M K < \<infinity>) \<and>
    (\<forall>a. distr M borel ((+) a) = M) \<and>
    (\<forall>U. open U \<longrightarrow> U \<noteq> {} \<longrightarrow> 0 < emeasure M U)"

theorem rademacher_s_theorem:
  fixes M :: "'e::real_normed_vector measure"
    and f :: "'e \<Rightarrow> 'f::real_normed_vector"
    and s :: "'e set"
    and C :: real
  assumes finite_dimensional_domain:
      "\<exists>BE :: 'e set.
        finite_dimensional_vector_space
          ((*\<^sub>R) :: real \<Rightarrow> 'e \<Rightarrow> 'e) BE"
    and finite_dimensional_codomain:
      "\<exists>BF :: 'f set.
        finite_dimensional_vector_space
          ((*\<^sub>R) :: real \<Rightarrow> 'f \<Rightarrow> 'f) BF"
    and haar_measure:
      "q132427_additive_haar_measure M"
    and measurable_set:
      "s \<in> sets M"
    and lipschitz:
      "C-lipschitz_on s f"
  shows
      "AE x in restrict_space M s.
        f differentiable (at x within s)"
  sorry

end
