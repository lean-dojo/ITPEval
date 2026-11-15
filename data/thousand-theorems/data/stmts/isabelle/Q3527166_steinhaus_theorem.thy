(*
  Statement-only formalization of the thousand-theorems corpus artifact Q3527166,
  "Steinhaus theorem": every measurable set of positive inner-regular left Haar
  measure in a locally compact topological group has a quotient set that is a
  neighborhood of the identity. This file contains no proof.
*)

theory Q3527166_steinhaus_theorem
  imports "HOL-Analysis.Borel_Space" "HOL-Analysis.Measure_Space"
begin

definition q3527166_topological_group ::
    "('a::topological_space \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
      ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" where
  "q3527166_topological_group mult ginv e \<longleftrightarrow>
    (\<forall>x y z. mult (mult x y) z = mult x (mult y z)) \<and>
    (\<forall>x. mult e x = x \<and> mult x e = x) \<and>
    (\<forall>x. mult (ginv x) x = e \<and> mult x (ginv x) = e) \<and>
    continuous_on UNIV
      (\<lambda>p :: 'a \<times> 'a. mult (fst p) (snd p)) \<and>
    continuous_on UNIV ginv"

definition q3527166_locally_compact ::
    "'a::topological_space itself \<Rightarrow> bool" where
  "q3527166_locally_compact _ \<longleftrightarrow>
    (\<forall>x :: 'a. \<forall>N.
      eventually (\<lambda>y. y \<in> N) (nhds x) \<longrightarrow>
      (\<exists>K. eventually (\<lambda>y. y \<in> K) (nhds x) \<and>
        K \<subseteq> N \<and> compact K))"

definition q3527166_left_haar_measure ::
    "('a::topological_space \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
      'a measure \<Rightarrow> bool" where
  "q3527166_left_haar_measure mult M \<longleftrightarrow>
    (\<forall>g A. A \<in> sets M \<longrightarrow>
      emeasure M (mult g ` A) = emeasure M A) \<and>
    (\<forall>K. compact K \<longrightarrow> emeasure M K < \<infinity>) \<and>
    (\<forall>U. open U \<longrightarrow> U \<noteq> {} \<longrightarrow> 0 < emeasure M U)"

definition q3527166_inner_regular ::
    "'a::topological_space measure \<Rightarrow> bool" where
  "q3527166_inner_regular M \<longleftrightarrow>
    (\<forall>A \<in> sets M. \<forall>r.
      r < emeasure M A \<longrightarrow>
      (\<exists>K. K \<subseteq> A \<and> compact K \<and> r < emeasure M K))"

definition q3527166_quotient_set ::
    "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
      ('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "q3527166_quotient_set mult ginv E =
    {z. \<exists>x \<in> E. \<exists>y \<in> E. z = mult x (ginv y)}"

theorem q3527166_steinhaus_theorem:
  fixes mult :: "'a::topological_space \<Rightarrow> 'a \<Rightarrow> 'a"
    and ginv :: "'a \<Rightarrow> 'a"
    and e :: "'a"
    and M :: "'a measure"
    and E :: "'a set"
  assumes topological_group:
      "q3527166_topological_group mult ginv e"
    and locally_compact:
      "q3527166_locally_compact TYPE('a)"
    and borel_space:
      "sets M = sets (borel :: 'a measure)"
    and haar_measure:
      "q3527166_left_haar_measure mult M"
    and inner_regular:
      "q3527166_inner_regular M"
    and measurable_set:
      "E \<in> sets M"
    and positive_measure:
      "0 < emeasure M E"
  shows
    "eventually
      (\<lambda>z. z \<in> q3527166_quotient_set mult ginv E)
      (nhds e)"
  sorry

end
