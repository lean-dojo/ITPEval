(*
  Statement-only formalization of thousand-theorems corpus artifact Q1050203,
  "Cantor's intersection theorem": a nonempty downward-directed family of
  nonempty compact closed sets has nonempty intersection. This file contains
  no proof.
*)

theory Q1050203_cantor_s_intersection_theorem
  imports "HOL.Topological_Spaces"
begin

theorem cantor_s_intersection:
  fixes S :: "'a::topological_space set set"
  assumes "S \<noteq> {}"
    and "\<And>U V. U \<in> S \<Longrightarrow> V \<in> S \<Longrightarrow>
      \<exists>W \<in> S. W \<subseteq> U \<and> W \<subseteq> V"
    and "\<And>U. U \<in> S \<Longrightarrow> U \<noteq> {}"
    and "\<And>U. U \<in> S \<Longrightarrow> compact U"
    and "\<And>U. U \<in> S \<Longrightarrow> closed U"
  shows "\<Inter>S \<noteq> {}"
  sorry

end
