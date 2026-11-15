(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q1477053 (thousand-theorems__isabelle__Q1477053), "Arzelà–Ascoli theorem":
  on a compact topological space, the uniform-metric closure of an
  equicontinuous family of bounded continuous functions whose values lie in a
  fixed compact set is compact. This file contains no proof.
*)

theory Q1477053_arzel_ascoli_theorem
  imports "HOL-Analysis.Bounded_Continuous_Function"
begin

definition q1477053_equicontinuous ::
    "('a::topological_space \<Rightarrow>\<^sub>C 'b::metric_space) set \<Rightarrow> bool"
  where
    "q1477053_equicontinuous A \<longleftrightarrow>
      (\<forall>x \<epsilon>. 0 < \<epsilon> \<longrightarrow>
        (\<exists>U. open U \<and> x \<in> U \<and>
          (\<forall>f \<in> A. \<forall>y \<in> U. \<forall>z \<in> U.
            dist (f y) (f z) < \<epsilon>)))"

theorem arzela_ascoli:
  fixes s :: "'b::metric_space set"
    and A :: "('a::topological_space \<Rightarrow>\<^sub>C 'b) set"
  assumes compact_domain: "compact (UNIV :: 'a set)"
    and compact_range: "compact s"
    and range_subset: "\<And>f x. f \<in> A \<Longrightarrow> f x \<in> s"
    and equicontinuous: "q1477053_equicontinuous A"
  shows "compact (closure A)"
  sorry

end
