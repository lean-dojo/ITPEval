(*
  Statement-only formalization of thousand-theorems corpus artifact Q1097021,
  "Minkowski's theorem": in a finite-dimensional real normed vector space, a
  convex set symmetric about zero whose additive Haar measure is greater than
  2 to the dimension times the measure of a fundamental domain of a countable
  additive subgroup contains a nonzero point of that subgroup. This file
  contains no proof.
*)

theory Q1097021_minkowski_s_theorem
  imports
    "HOL-Analysis.Convex"
    "HOL-Analysis.Complete_Measure"
begin

definition q1097021_finite_dimensional ::
    "'a::real_vector itself \<Rightarrow> bool" where
  "q1097021_finite_dimensional _ \<longleftrightarrow>
    (\<exists>B :: 'a set. finite_dimensional_vector_space ((*\<^sub>R)) B)"

definition q1097021_dimension ::
    "'a::real_vector itself \<Rightarrow> nat" where
  "q1097021_dimension _ = dim (UNIV :: 'a set)"

definition q1097021_null_measurable ::
    "'a measure \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q1097021_null_measurable M A \<longleftrightarrow>
    (\<exists>B \<in> sets M. AE x in M. (x \<in> A) = (x \<in> B))"

definition q1097021_add_subgroup ::
    "'a::ab_group_add set \<Rightarrow> bool" where
  "q1097021_add_subgroup L \<longleftrightarrow>
    0 \<in> L \<and>
    (\<forall>x \<in> L. \<forall>y \<in> L. x + y \<in> L) \<and>
    (\<forall>x \<in> L. -x \<in> L)"

definition q1097021_translate ::
    "'a::ab_group_add \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "q1097021_translate a A = ((+) a) ` A"

definition q1097021_is_add_haar_measure ::
    "'a::real_normed_vector measure \<Rightarrow> bool" where
  "q1097021_is_add_haar_measure M \<longleftrightarrow>
    (\<forall>a A. A \<in> sets M \<longrightarrow>
      emeasure M (q1097021_translate a A) = emeasure M A) \<and>
    (\<forall>K. compact K \<longrightarrow> emeasure M K < \<infinity>) \<and>
    (\<forall>U. open U \<longrightarrow> U \<noteq> {} \<longrightarrow> 0 < emeasure M U)"

definition q1097021_is_add_fundamental_domain ::
    "'a::ab_group_add set \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "q1097021_is_add_fundamental_domain L F M \<longleftrightarrow>
    q1097021_null_measurable M F \<and>
    (AE x in M. \<exists>a \<in> L. a + x \<in> F) \<and>
    (\<forall>a \<in> L. \<forall>b \<in> L. a \<noteq> b \<longrightarrow>
      (AE x in M.
        \<not> (x \<in> q1097021_translate a F \<and>
          x \<in> q1097021_translate b F)))"

theorem minkowski_s_theorem:
  fixes M :: "'a::real_normed_vector measure"
    and L F S :: "'a set"
  assumes borel_space:
      "sets M = sets (borel :: 'a measure)"
    and finite_dimensional:
      "q1097021_finite_dimensional TYPE('a)"
    and haar_measure:
      "q1097021_is_add_haar_measure M"
    and subgroup:
      "q1097021_add_subgroup L"
    and countable_subgroup:
      "countable L"
    and fundamental_domain:
      "q1097021_is_add_fundamental_domain L F M"
    and symmetric:
      "\<And>x. x \<in> S \<Longrightarrow> -x \<in> S"
    and convex:
      "convex S"
    and large_measure:
      "outer_measure_of M F * (2::ennreal) ^ q1097021_dimension TYPE('a) <
        outer_measure_of M S"
  shows
      "\<exists>x \<in> L. x \<noteq> 0 \<and> x \<in> S"
  sorry

end
