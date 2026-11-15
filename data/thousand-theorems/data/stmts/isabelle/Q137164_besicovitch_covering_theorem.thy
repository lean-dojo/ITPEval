(*
  Statement-only formalization of the thousand-theorems corpus artifact Q137164,
  "Besicovitch covering theorem": in a second-countable metric space with the
  Besicovitch covering property, a family of admissible radii accumulating at
  zero yields a countable pairwise-disjoint family of closed balls covering a
  given set up to an outer-null remainder, with prescribed positive pointwise
  radius bounds. This file contains no proof.
*)

theory Q137164_besicovitch_covering_theorem
  imports "HOL-Analysis.Borel_Space" "HOL-Analysis.Measure_Space"
begin

definition q137164_satellite_configuration ::
    "nat \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> 'a::metric_space) \<Rightarrow>
      (nat \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q137164_satellite_configuration N tau c rad \<longleftrightarrow>
      (\<forall>i < Suc N. 0 < rad i) \<and>
      (\<forall>i < Suc N. \<forall>j < Suc N. i \<noteq> j \<longrightarrow>
        ((rad i \<le> dist (c i) (c j) \<and> rad j \<le> tau * rad i) \<or>
         (rad j \<le> dist (c j) (c i) \<and> rad i \<le> tau * rad j))) \<and>
      (\<forall>i < N.
        rad i \<le> dist (c i) (c N) \<and> rad N \<le> tau * rad i) \<and>
      (\<forall>i < N. dist (c i) (c N) \<le> rad i + rad N)"

definition q137164_has_besicovitch_covering ::
    "'a::metric_space itself \<Rightarrow> bool"
  where
    "q137164_has_besicovitch_covering _ \<longleftrightarrow>
      (\<exists>N tau. 1 < tau \<and>
        \<not> (\<exists>c rad.
          q137164_satellite_configuration N tau
            (c :: nat \<Rightarrow> 'a) rad))"

definition q137164_s_finite_measure :: "'a measure \<Rightarrow> bool"
  where
    "q137164_s_finite_measure M \<longleftrightarrow>
      (\<exists>Ms :: nat \<Rightarrow> 'a measure.
        (\<forall>n. sets (Ms n) = sets M \<and>
          emeasure (Ms n) (space M) \<noteq> \<infinity>) \<and>
        (\<forall>A.
          emeasure M A = (\<Sum>n. emeasure (Ms n) A)))"

definition q137164_outer_null ::
    "'a measure \<Rightarrow> 'a set \<Rightarrow> bool"
  where
    "q137164_outer_null M A \<longleftrightarrow>
      (\<exists>u \<in> sets M. A \<subseteq> u \<and> emeasure M u = 0)"

theorem besicovitch_covering_theorem:
  fixes M :: "'a::{metric_space,second_countable_topology} measure"
    and f :: "'a \<Rightarrow> real set"
    and s :: "'a set"
    and R :: "'a \<Rightarrow> real"
  assumes measurable_space:
      "space M = UNIV"
      "sets borel \<subseteq> sets M"
    and s_finite:
      "q137164_s_finite_measure M"
    and besicovitch:
      "q137164_has_besicovitch_covering TYPE('a)"
    and arbitrarily_small:
      "\<And>x delta. x \<in> s \<Longrightarrow> 0 < delta \<Longrightarrow>
        \<exists>rho \<in> f x. 0 < rho \<and> rho < delta"
    and radius_bound:
      "\<And>x. x \<in> s \<Longrightarrow> 0 < R x"
  shows
      "\<exists>t r. countable t \<and> t \<subseteq> s \<and>
        (\<forall>x \<in> t. r x \<in> f x \<and> 0 < r x \<and> r x < R x) \<and>
        q137164_outer_null M
          (s - (\<Union>x\<in>t. cball x (r x))) \<and>
        pairwise
          (\<lambda>x y. disjnt (cball x (r x)) (cball y (r y))) t"
  sorry

end
