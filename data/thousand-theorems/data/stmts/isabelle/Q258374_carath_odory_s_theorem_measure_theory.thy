(*
  Statement-only formalization of the thousand-theorems corpus artifact Q258374,
  "Carathéodory's theorem (measure theory)": the sets satisfying the
  Carathéodory splitting criterion for an outer measure form a measurable
  space. This file contains no proof.
*)

theory Q258374_carath_odory_s_theorem_measure_theory
  imports "HOL-Analysis.Caratheodory"
begin

definition q258374_caratheodory_sets ::
    "('a set \<Rightarrow> ennreal) \<Rightarrow> 'a set set"
  where
    "q258374_caratheodory_sets m =
      {s. \<forall>t. m t = m (t \<inter> s) + m (t - s)}"

theorem q258374_caratheodory:
  fixes m :: "'a set \<Rightarrow> ennreal"
  assumes outer_measure: "outer_measure_space (Pow UNIV) m"
  shows "sigma_algebra UNIV (q258374_caratheodory_sets m)"
  sorry

end
