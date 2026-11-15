(*
  Statement-only formalization of the thousand-theorems corpus artifact Q226014
  (thousand-theorems__isabelle__Q226014), "Poincaré recurrence theorem": for a
  conservative nonsingular measurable self-map of an arbitrary measure space,
  almost every point of a null-measurable set returns to that set infinitely
  often. This file contains no proof.
*)

theory Q226014_poincare_recurrence_theorem
  imports "HOL-Analysis.Complete_Measure"
begin

definition q226014_quasi_measure_preserving ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where
    "q226014_quasi_measure_preserving M f \<longleftrightarrow>
      f \<in> measurable M M \<and>
      (\<forall>N \<in> null_sets M. f -` N \<in> null_sets M)"

definition q226014_null_measurable_set ::
    "'a measure \<Rightarrow> 'a set \<Rightarrow> bool"
  where
    "q226014_null_measurable_set M s \<longleftrightarrow>
      (\<exists>t \<in> sets M. \<exists>N \<in> null_sets M.
        (s - t) \<union> (t - s) \<subseteq> N)"

definition q226014_conservative ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where
    "q226014_conservative M f \<longleftrightarrow>
      q226014_quasi_measure_preserving M f \<and>
      (\<forall>u \<in> sets M.
        emeasure M u \<noteq> 0 \<longrightarrow>
        (\<exists>x \<in> u. \<exists>m :: nat.
          m \<noteq> 0 \<and> (f ^^ m) x \<in> u))"

theorem poincare_recurrence_theorem:
  fixes M :: "'a measure"
    and f :: "'a \<Rightarrow> 'a"
    and s :: "'a set"
  assumes full_space: "space M = UNIV"
    and conservative: "q226014_conservative M f"
    and null_measurable: "q226014_null_measurable_set M s"
  shows
    "AE x in M.
      x \<in> s \<longrightarrow>
      frequently (\<lambda>n :: nat. (f ^^ n) x \<in> s) at_top"
  sorry

end
