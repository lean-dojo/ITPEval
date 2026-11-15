(*
  Statement-only formalization of the thousand-theorems corpus artifact Q2027347,
  "Optional stopping theorem": a strongly adapted integrable real-valued
  discrete-time process is a submartingale exactly when expected stopped values
  are monotone for every ordered pair of bounded stopping times. This file
  contains no proof.
*)

theory Q2027347_optional_stopping_theorem
  imports "HOL-Analysis.Set_Integral" "HOL-Library.Extended_Nat"
begin

definition q2027347_filtration ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a measure) \<Rightarrow> bool" where
  "q2027347_filtration M F \<longleftrightarrow>
    space M = UNIV \<and>
    (\<forall>n. space (F n) = UNIV \<and> sets (F n) \<subseteq> sets M) \<and>
    (\<forall>i j. i \<le> j \<longrightarrow> sets (F i) \<subseteq> sets (F j))"

definition q2027347_filtered_measure ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a measure) \<Rightarrow> nat \<Rightarrow> 'a measure" where
  "q2027347_filtered_measure M F n =
    measure_of UNIV (sets (F n)) (emeasure M)"

definition q2027347_sigma_finite_filtration ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a measure) \<Rightarrow> bool" where
  "q2027347_sigma_finite_filtration M F \<longleftrightarrow>
    (\<forall>n. sigma_finite_measure (q2027347_filtered_measure M F n))"

definition q2027347_strongly_adapted ::
    "(nat \<Rightarrow> 'a measure) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "q2027347_strongly_adapted F f \<longleftrightarrow>
    (\<forall>n. f n \<in> borel_measurable (F n))"

definition q2027347_stopping_time ::
    "(nat \<Rightarrow> 'a measure) \<Rightarrow> ('a \<Rightarrow> enat) \<Rightarrow> bool" where
  "q2027347_stopping_time F T \<longleftrightarrow>
    (\<forall>n. Measurable.pred (F n) (\<lambda>x. T x \<le> enat n))"

definition q2027347_stopped_value ::
    "(nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> enat) \<Rightarrow> 'a \<Rightarrow> real" where
  "q2027347_stopped_value f T x =
    (case T x of enat n \<Rightarrow> f n x | \<infinity> \<Rightarrow> f 0 x)"

definition q2027347_submartingale ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a measure) \<Rightarrow>
      (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "q2027347_submartingale M F f \<longleftrightarrow>
    q2027347_strongly_adapted F f \<and>
    (\<forall>n. integrable M (f n)) \<and>
    (\<forall>i j A.
      i \<le> j \<longrightarrow>
      A \<in> sets (F i) \<longrightarrow>
      set_lebesgue_integral M A (f i) \<le>
        set_lebesgue_integral M A (f j))"

theorem submartingale_iff_expected_stopped_value_mono:
  fixes M :: "'a measure"
    and F :: "nat \<Rightarrow> 'a measure"
    and f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes filtration: "q2027347_filtration M F"
    and sigma_finite: "q2027347_sigma_finite_filtration M F"
    and adapted: "q2027347_strongly_adapted F f"
    and integrable: "\<forall>n. integrable M (f n)"
  shows
    "q2027347_submartingale M F f \<longleftrightarrow>
      (\<forall>T S.
        q2027347_stopping_time F T \<longrightarrow>
        q2027347_stopping_time F S \<longrightarrow>
        (\<forall>x. T x \<le> S x) \<longrightarrow>
        (\<exists>N::nat. \<forall>x. S x \<le> enat N) \<longrightarrow>
        lebesgue_integral M (q2027347_stopped_value f T) \<le>
          lebesgue_integral M (q2027347_stopped_value f S))"
  sorry

end
