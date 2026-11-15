(*
  Statement-only formalization of the thousand-theorems corpus artifact Q2275191,
  "Lebesgue differentiation theorem": an almost-everywhere measurable
  extended-nonnegative function with finite lower integral is recovered almost
  everywhere as the limit of its local integral averages along a Vitali family.
  This file contains no proof.
*)

theory Q2275191_lebesgue_differentiation_theorem
  imports "HOL-Analysis.Set_Integral"
begin

definition q2275191_pseudometric ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q2275191_pseudometric d \<longleftrightarrow>
      (\<forall>x. d x x = 0) \<and>
      (\<forall>x y. 0 \<le> d x y) \<and>
      (\<forall>x y. d x y = d y x) \<and>
      (\<forall>x y z. d x z \<le> d x y + d y z)"

definition q2275191_ball ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a set"
  where
    "q2275191_ball d x r = {y. d y x < r}"

definition q2275191_cball ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a set"
  where
    "q2275191_cball d x r = {y. d y x \<le> r}"

definition q2275191_open ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> bool"
  where
    "q2275191_open d U \<longleftrightarrow>
      (\<forall>x \<in> U. \<exists>r > 0. q2275191_ball d x r \<subseteq> U)"

definition q2275191_interior ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where
    "q2275191_interior d A =
      {x. \<exists>r > 0. q2275191_ball d x r \<subseteq> A}"

definition q2275191_second_countable ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q2275191_second_countable d \<longleftrightarrow>
      (\<exists>B :: 'a set set.
        countable B \<and>
        (\<forall>A \<in> B. q2275191_open d A) \<and>
        (\<forall>U x. q2275191_open d U \<longrightarrow> x \<in> U \<longrightarrow>
          (\<exists>A \<in> B. x \<in> A \<and> A \<subseteq> U)))"

definition q2275191_borel_measure ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a measure \<Rightarrow> bool"
  where
    "q2275191_borel_measure d M \<longleftrightarrow>
      space M = UNIV \<and>
      sets M = sigma_sets UNIV {U. q2275191_open d U}"

definition q2275191_locally_finite ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a measure \<Rightarrow> bool"
  where
    "q2275191_locally_finite d M \<longleftrightarrow>
      (\<forall>x. \<exists>U. q2275191_open d U \<and> x \<in> U \<and>
        emeasure M U < \<infinity>)"

definition q2275191_outer_null ::
    "'a measure \<Rightarrow> 'a set \<Rightarrow> bool"
  where
    "q2275191_outer_null M A \<longleftrightarrow>
      (\<exists>N \<in> sets M. A \<subseteq> N \<and> emeasure M N = 0)"

definition q2275191_vitali_family ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a measure \<Rightarrow>
      ('a \<Rightarrow> 'a set set) \<Rightarrow> bool"
  where
    "q2275191_vitali_family d M V \<longleftrightarrow>
      (\<forall>x A. A \<in> V x \<longrightarrow>
        A \<in> sets M \<and> q2275191_interior d A \<noteq> {}) \<and>
      (\<forall>x r. 0 < r \<longrightarrow>
        (\<exists>A \<in> V x. A \<subseteq> q2275191_cball d x r)) \<and>
      (\<forall>s F.
        (\<forall>x \<in> s. F x \<subseteq> V x) \<longrightarrow>
        (\<forall>x \<in> s. \<forall>r > 0.
          \<exists>A \<in> F x. A \<subseteq> q2275191_cball d x r) \<longrightarrow>
        (\<exists>T :: ('a \<times> 'a set) set.
          (\<forall>p \<in> T. fst p \<in> s) \<and>
          pairwise (\<lambda>p q. disjnt (snd p) (snd q)) T \<and>
          (\<forall>p \<in> T. snd p \<in> F (fst p)) \<and>
          q2275191_outer_null M
            (s - (\<Union>p\<in>T. snd p))))"

definition q2275191_filter_at ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a set set) \<Rightarrow>
      'a \<Rightarrow> ('a set) filter"
  where
    "q2275191_filter_at d V x =
      (INF r\<in>{r::real. 0 < r}.
        principal {A. A \<in> V x \<and> A \<subseteq> q2275191_cball d x r})"

definition q2275191_ae_measurable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> bool"
  where
    "q2275191_ae_measurable M f \<longleftrightarrow>
      (\<exists>g \<in> borel_measurable M. AE x in M. f x = g x)"

definition q2275191_set_lintegral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> 'a set \<Rightarrow> ennreal"
  where
    "q2275191_set_lintegral M f A =
      nn_integral M (\<lambda>x. indicator A x * f x)"

theorem lebesgue_differentiation_theorem:
  fixes d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
    and M :: "'a measure"
    and V :: "'a \<Rightarrow> 'a set set"
    and f :: "'a \<Rightarrow> ennreal"
  assumes pseudometric:
      "q2275191_pseudometric d"
    and second_countable:
      "q2275191_second_countable d"
    and borel_measure:
      "q2275191_borel_measure d M"
    and locally_finite:
      "q2275191_locally_finite d M"
    and vitali_family:
      "q2275191_vitali_family d M V"
    and f_ae_measurable:
      "q2275191_ae_measurable M f"
    and f_finite:
      "nn_integral M f \<noteq> \<infinity>"
  shows
      "AE x in M.
        filterlim
          (\<lambda>A. q2275191_set_lintegral M f A / emeasure M A)
          (nhds (f x))
          (q2275191_filter_at d V x)"
  sorry

end
