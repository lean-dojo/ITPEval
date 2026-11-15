(*
  Statement-only formalization of thousand-theorems corpus artifact Q3527102,
  "Kruskal–Katona theorem": among uniform finite set families of bounded
  natural subsets, a colexicographic initial segment has no larger one-step
  shadow than any family with at least as many members. This file contains no
  proof.
*)

theory Q3527102_kruskal_katona_theorem
  imports Main
begin

definition q3527102_family_on :: "nat \<Rightarrow> nat set set \<Rightarrow> bool" where
  "q3527102_family_on n F \<longleftrightarrow>
    finite F \<and> F \<subseteq> Pow {..<n}"

definition q3527102_uniform_family_on ::
    "nat \<Rightarrow> nat \<Rightarrow> nat set set \<Rightarrow> bool" where
  "q3527102_uniform_family_on n r F \<longleftrightarrow>
    q3527102_family_on n F \<and> (\<forall>S \<in> F. card S = r)"

definition q3527102_colex_less :: "nat set \<Rightarrow> nat set \<Rightarrow> bool" where
  "q3527102_colex_less S T \<longleftrightarrow>
    S \<noteq> T \<and>
    (\<forall>a \<in> S - T. \<exists>b \<in> T - S. a < b)"

definition q3527102_initial_colex_segment_on ::
    "nat \<Rightarrow> nat \<Rightarrow> nat set set \<Rightarrow> bool" where
  "q3527102_initial_colex_segment_on n r C \<longleftrightarrow>
    q3527102_uniform_family_on n r C \<and>
    (\<forall>S \<in> C. \<forall>T.
      T \<subseteq> {..<n} \<longrightarrow>
      card T = r \<longrightarrow>
      q3527102_colex_less T S \<longrightarrow>
      T \<in> C)"

definition q3527102_shadow :: "nat set set \<Rightarrow> nat set set" where
  "q3527102_shadow F =
    {T. \<exists>S \<in> F. \<exists>a \<in> S. T = S - {a}}"

theorem q3527102_kruskal_katona:
  fixes n r :: nat
    and A C :: "nat set set"
  assumes uniform_A: "q3527102_uniform_family_on n r A"
    and size_C_le_A: "card C \<le> card A"
    and initial_C: "q3527102_initial_colex_segment_on n r C"
  shows "card (q3527102_shadow C) \<le> card (q3527102_shadow A)"
  sorry

end
