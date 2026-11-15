(*
  Statement-only formalization of the thousand-theorems corpus artifact Q190391
  (thousand-theorems__isabelle__Q190391), "Central limit theorem": independent
  identically distributed real random variables with a finite second moment,
  centered and scaled by the square root of the sample size, converge in
  distribution to the centered Gaussian law with their common variance. This
  includes the zero-variance case. This file contains no proof.
*)

theory Q190391_central_limit_theorem
  imports
    "HOL-Analysis.Set_Integral"
    "HOL-Analysis.Lebesgue_Measure"
begin

definition q190391_probability_measure :: "'a measure \<Rightarrow> bool"
  where
    "q190391_probability_measure M \<longleftrightarrow>
      emeasure M (space M) = 1"

definition q190391_measurable_representative ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q190391_measurable_representative M f g \<longleftrightarrow>
      g \<in> borel_measurable M \<and> (AE x in M. f x = g x)"

definition q190391_has_law ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real measure \<Rightarrow> bool"
  where
    "q190391_has_law M f \<mu> \<longleftrightarrow>
      (\<exists>g. q190391_measurable_representative M f g \<and>
        distr M borel g = \<mu>)"

definition q190391_identically_distributed ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q190391_identically_distributed M f g \<longleftrightarrow>
      (\<exists>f' g'.
        q190391_measurable_representative M f f' \<and>
        q190391_measurable_representative M g g' \<and>
        distr M borel f' = distr M borel g')"

definition q190391_mem_L2 ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q190391_mem_L2 M f \<longleftrightarrow>
      (\<exists>g. q190391_measurable_representative M f g \<and>
        integrable M (\<lambda>x. (g x)\<^sup>2))"

definition q190391_measurable_version ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real"
  where
    "q190391_measurable_version M f =
      (SOME g. q190391_measurable_representative M f g)"

definition q190391_event ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> 'a set"
  where
    "q190391_event M f A = f -` A \<inter> space M"

definition q190391_joint_event ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow>
      nat set \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 'a set"
  where
    "q190391_joint_event M X J A =
      {\<omega> \<in> space M. \<forall>j\<in>J. X j \<omega> \<in> A j}"

definition q190391_independent ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q190391_independent M X \<longleftrightarrow>
      (\<exists>X'.
        (\<forall>n. q190391_measurable_representative M (X n) (X' n)) \<and>
        (\<forall>J::nat set.
          finite J \<longrightarrow> J \<noteq> {} \<longrightarrow>
          (\<forall>A::nat \<Rightarrow> real set.
            (\<forall>j\<in>J. A j \<in> sets borel) \<longrightarrow>
            measure M (q190391_joint_event M X' J A) =
              prod
                (\<lambda>j. measure M (q190391_event M (X' j) (A j)))
                J)))"

definition q190391_expectation ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real"
  where
    "q190391_expectation M f =
      integral\<^sup>L M (q190391_measurable_version M f)"

definition q190391_variance ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real"
  where
    "q190391_variance M f =
      integral\<^sup>L M
        (\<lambda>x.
          (q190391_measurable_version M f x -
            q190391_expectation M f)\<^sup>2)"

definition q190391_standard_normal :: "real measure"
  where
    "q190391_standard_normal =
      density (lborel :: real measure)
        (\<lambda>x. ennreal
          ((1 / sqrt (2 * pi)) * exp (-(x\<^sup>2) / 2)))"

definition q190391_gaussian_real :: "real \<Rightarrow> real measure"
  where
    "q190391_gaussian_real v =
      distr q190391_standard_normal borel
        (\<lambda>z. sqrt (max v 0) * z)"

definition q190391_weak_convergence ::
    "(nat \<Rightarrow> real measure) \<Rightarrow> real measure \<Rightarrow> bool"
  where
    "q190391_weak_convergence Ms M \<longleftrightarrow>
      (\<forall>x.
        isCont (\<lambda>t. measure M {..t}) x \<longrightarrow>
        (\<lambda>n. measure (Ms n) {..x})
          \<longlonglongrightarrow> measure M {..x})"

definition q190391_tendsto_in_distribution ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow>
      'b measure \<Rightarrow> ('b \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q190391_tendsto_in_distribution M Z N Y \<longleftrightarrow>
      (\<exists>Z' Y'.
        (\<forall>n. q190391_measurable_representative M (Z n) (Z' n)) \<and>
        q190391_measurable_representative N Y Y' \<and>
        q190391_weak_convergence
          (\<lambda>n. distr M borel (Z' n))
          (distr N borel Y'))"

theorem central_limit_theorem:
  fixes P :: "'a measure"
    and P' :: "'b measure"
    and X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and Y :: "'b \<Rightarrow> real"
  assumes P_probability: "q190391_probability_measure P"
    and P'_probability: "q190391_probability_measure P'"
    and Y_law:
      "q190391_has_law P' Y
        (q190391_gaussian_real (q190391_variance P (X 0)))"
    and X_second_moment: "q190391_mem_L2 P (X 0)"
    and X_independent: "q190391_independent P X"
    and X_identically_distributed:
      "\<And>i. q190391_identically_distributed P (X i) (X 0)"
  shows
    "q190391_tendsto_in_distribution P
      (\<lambda>n \<omega>.
        inverse (sqrt (real n)) *
          ((\<Sum>k<n. X k \<omega>) -
            real n * q190391_expectation P (X 0)))
      P' Y"
  sorry

end
