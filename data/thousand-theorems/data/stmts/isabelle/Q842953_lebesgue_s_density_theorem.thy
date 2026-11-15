(*
  Statement-only formalization of the thousand-theorems corpus artifact Q842953,
  "Lebesgue's density theorem": in a second-countable metric space with the
  Besicovitch covering property, every set has density one almost everywhere
  with respect to the outer-measure restriction of any locally finite Borel
  measure, along closed balls whose positive radii tend to zero. This file
  contains no proof.
*)

theory Q842953_lebesgue_s_density_theorem
  imports "HOL-Analysis.Borel_Space" "HOL-Analysis.Measure_Space"
begin

definition q842953_satellite_configuration ::
    "nat \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> 'a::metric_space) \<Rightarrow>
      (nat \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q842953_satellite_configuration N tau c rad \<longleftrightarrow>
      (\<forall>i < Suc N. 0 < rad i) \<and>
      (\<forall>i < Suc N. \<forall>j < Suc N. i \<noteq> j \<longrightarrow>
        ((rad i \<le> dist (c i) (c j) \<and> rad j \<le> tau * rad i) \<or>
         (rad j \<le> dist (c j) (c i) \<and> rad i \<le> tau * rad j))) \<and>
      (\<forall>i < N.
        rad i \<le> dist (c i) (c N) \<and> rad N \<le> tau * rad i) \<and>
      (\<forall>i < N. dist (c i) (c N) \<le> rad i + rad N)"

definition q842953_has_besicovitch_covering ::
    "'a::metric_space itself \<Rightarrow> bool"
  where
    "q842953_has_besicovitch_covering _ \<longleftrightarrow>
      (\<exists>N tau. 1 < tau \<and>
        \<not> (\<exists>c rad.
          q842953_satellite_configuration N tau
            (c :: nat \<Rightarrow> 'a) rad))"

definition q842953_locally_finite_measure ::
    "'a::metric_space measure \<Rightarrow> bool"
  where
    "q842953_locally_finite_measure M \<longleftrightarrow>
      (\<forall>x. \<exists>U. open U \<and> x \<in> U \<and> emeasure M U < \<infinity>)"

definition q842953_outer_measure ::
    "'a measure \<Rightarrow> 'a set \<Rightarrow> ennreal"
  where
    "q842953_outer_measure M A =
      Inf {emeasure M B | B. B \<in> sets M \<and> A \<subseteq> B}"

definition q842953_almost_everywhere_on ::
    "'a measure \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where
    "q842953_almost_everywhere_on M s P \<longleftrightarrow>
      q842953_outer_measure M {x \<in> s. \<not> P x} = 0"

theorem lebesgue_s_density_theorem:
  fixes M :: "'a::{metric_space,second_countable_topology} measure"
    and s :: "'a set"
  assumes borel_measure:
      "sets M = sets borel"
    and locally_finite:
      "q842953_locally_finite_measure M"
    and besicovitch:
      "q842953_has_besicovitch_covering TYPE('a)"
  shows
      "q842953_almost_everywhere_on M s
        (\<lambda>x.
          filterlim
            (\<lambda>r.
              q842953_outer_measure M (s \<inter> cball x r) /
                q842953_outer_measure M (cball x r))
            (nhds 1)
            (at_right 0))"
  sorry

end
