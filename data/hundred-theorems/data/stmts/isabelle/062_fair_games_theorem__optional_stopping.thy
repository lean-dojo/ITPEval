(*
  Statement-only formalization of Hundred Theorems artifact 062,
  "Fair Games Theorem (Optional Stopping)": discrete-time martingale,
  submartingale, and supermartingale expectation laws at stopping times.
  This file contains no proof.
*)

theory Fair_Games_Theorem_Optional_Stopping
  imports
    "HOL-Probability.Conditional_Expectation"
    "HOL-Probability.Stopping_Time"
begin

definition adapted_process ::
    "(nat \<Rightarrow> 'a measure) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "adapted_process F X \<longleftrightarrow>
      (\<forall>n. X n \<in> borel_measurable (F n))"

definition integrable_process ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "integrable_process M X \<longleftrightarrow> (\<forall>n. integrable M (X n))"

definition martingale_process ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a measure) \<Rightarrow>
      (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "martingale_process M F X \<longleftrightarrow>
      (\<forall>n. AE \<omega> in M.
        real_cond_exp M (F n) (X (Suc n)) \<omega> = X n \<omega>)"

definition submartingale_process ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a measure) \<Rightarrow>
      (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "submartingale_process M F X \<longleftrightarrow>
      (\<forall>n. AE \<omega> in M.
        X n \<omega> \<le> real_cond_exp M (F n) (X (Suc n)) \<omega>)"

definition supermartingale_process ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a measure) \<Rightarrow>
      (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "supermartingale_process M F X \<longleftrightarrow>
      (\<forall>n. AE \<omega> in M.
        real_cond_exp M (F n) (X (Suc n)) \<omega> \<le> X n \<omega>)"

definition extended_filtration ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a measure) \<Rightarrow> enat \<Rightarrow> 'a measure"
  where
    "extended_filtration M F t =
      (case t of enat n \<Rightarrow> F n | \<infinity> \<Rightarrow> M)"

definition discrete_stopping_time ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a measure) \<Rightarrow> ('a \<Rightarrow> enat) \<Rightarrow> bool"
  where
    "discrete_stopping_time M F T \<longleftrightarrow>
      stopping_time (extended_filtration M F) T"

definition stopped_value ::
    "(nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> enat) \<Rightarrow> 'a \<Rightarrow> real"
  where
    "stopped_value X T \<omega> =
      (case T \<omega> of enat n \<Rightarrow> X n \<omega> | \<infinity> \<Rightarrow> 0)"

definition optional_stopping_conditions ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> enat) \<Rightarrow>
      (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "optional_stopping_conditions M T X \<longleftrightarrow>
      ((\<exists>N::nat. AE \<omega> in M. T \<omega> \<le> enat N) \<or>
       ((AE \<omega> in M. T \<omega> \<noteq> \<infinity>) \<and>
        (\<exists>K::real. \<forall>n. AE \<omega> in M. abs (X n \<omega>) < K)) \<or>
       ((AE \<omega> in M. T \<omega> \<noteq> \<infinity>) \<and>
        integrable M (\<lambda>\<omega>. real (the_enat (T \<omega>))) \<and>
        (\<exists>K::real. \<forall>n. AE \<omega> in M.
          abs (X (Suc n) \<omega> - X n \<omega>) \<le> K)))"

theorem submartingale_iff_expected_stopped_value_mono:
  fixes M :: "'a measure"
    and F :: "nat \<Rightarrow> 'a measure"
    and X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "filtration (space M) F"
    and "\<And>n. sigma_finite_subalgebra M (F n)"
    and "adapted_process F X"
    and "integrable_process M X"
  shows "submartingale_process M F X \<longleftrightarrow>
    (\<forall>T S :: 'a \<Rightarrow> enat.
      discrete_stopping_time M F T \<longrightarrow>
      discrete_stopping_time M F S \<longrightarrow>
      (\<forall>\<omega>. T \<omega> \<le> S \<omega>) \<longrightarrow>
      (\<exists>N::nat. \<forall>\<omega>. S \<omega> \<le> enat N) \<longrightarrow>
      (\<integral>\<omega>. stopped_value X T \<omega> \<partial>M) \<le>
        (\<integral>\<omega>. stopped_value X S \<omega> \<partial>M))"
  sorry

theorem fair_games_optional_stopping:
  fixes M :: "'a measure"
    and F :: "nat \<Rightarrow> 'a measure"
    and X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and T :: "'a \<Rightarrow> enat"
  assumes "prob_space M"
    and "filtration (space M) F"
    and "\<And>n. subalgebra M (F n)"
    and "adapted_process F X"
    and "integrable_process M X"
    and "discrete_stopping_time M F T"
    and "optional_stopping_conditions M T X"
    and "martingale_process M F X"
  shows "(\<integral>\<omega>. stopped_value X T \<omega> \<partial>M) =
    (\<integral>\<omega>. X 0 \<omega> \<partial>M)"
  sorry

theorem submartingale_optional_stopping:
  fixes M :: "'a measure"
    and F :: "nat \<Rightarrow> 'a measure"
    and X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and T :: "'a \<Rightarrow> enat"
  assumes "prob_space M"
    and "filtration (space M) F"
    and "\<And>n. subalgebra M (F n)"
    and "adapted_process F X"
    and "integrable_process M X"
    and "discrete_stopping_time M F T"
    and "optional_stopping_conditions M T X"
    and "submartingale_process M F X"
  shows "(\<integral>\<omega>. X 0 \<omega> \<partial>M) \<le>
    (\<integral>\<omega>. stopped_value X T \<omega> \<partial>M)"
  sorry

theorem supermartingale_optional_stopping:
  fixes M :: "'a measure"
    and F :: "nat \<Rightarrow> 'a measure"
    and X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and T :: "'a \<Rightarrow> enat"
  assumes "prob_space M"
    and "filtration (space M) F"
    and "\<And>n. subalgebra M (F n)"
    and "adapted_process F X"
    and "integrable_process M X"
    and "discrete_stopping_time M F T"
    and "optional_stopping_conditions M T X"
    and "supermartingale_process M F X"
  shows "(\<integral>\<omega>. stopped_value X T \<omega> \<partial>M) \<le>
    (\<integral>\<omega>. X 0 \<omega> \<partial>M)"
  sorry

end
