(*
  Statement-only formalization of the thousand-theorems corpus artifact Q182505
  (thousand-theorems__isabelle__Q182505), "Bayes' theorem": for two measurable
  events in an arbitrary finite measure space, conditional probability is the
  inverse measure of the conditioning event times the intersection measure,
  and satisfies Bayes' identity. This file contains no proof.
*)

theory Q182505_bayes_theorem
  imports "HOL-Analysis.Measure_Space"
begin

definition q182505_conditional_probability ::
    "'a measure \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> ennreal"
  where
    "q182505_conditional_probability M t s =
      inverse (emeasure M s) * emeasure M (s \<inter> t)"

theorem bayes_theorem:
  fixes M :: "'a measure"
    and s t :: "'a set"
  assumes finite_measure: "finite_measure M"
    and s_measurable: "s \<in> sets M"
    and t_measurable: "t \<in> sets M"
  shows
    "q182505_conditional_probability M t s =
      inverse (emeasure M s) *
        q182505_conditional_probability M s t * emeasure M t"
  sorry

end
