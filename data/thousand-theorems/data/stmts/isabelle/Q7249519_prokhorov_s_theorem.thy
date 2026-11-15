(*
  Statement-only formalization of the thousand-theorems corpus artifact Q7249519
  (thousand-theorems__isabelle__Q7249519), "Prokhorov's theorem": on an
  arbitrary Hausdorff Borel space, finite measures with uniformly bounded mass
  and uniformly vanishing mass outside compact sets form a compact set in the
  weak topology, assuming normality or monotonicity of the compact sets. This
  file contains no proof.
*)

theory Q7249519_prokhorov_s_theorem
  imports
    "HOL-Analysis.Abstract_Topological_Spaces"
    "HOL-Analysis.Bochner_Integration"
begin

definition q7249519_finite_borel_measures ::
    "'a::topological_space measure set"
  where
    "q7249519_finite_borel_measures =
      {M. sets M = sets borel \<and> finite_measure M}"

definition q7249519_bounded_continuous ::
    "('a::topological_space \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q7249519_bounded_continuous f \<longleftrightarrow>
      bounded (range f) \<and> continuous_on UNIV f"

definition q7249519_weak_topology ::
    "'a::topological_space measure topology"
  where
    "q7249519_weak_topology =
      topology_generated_by
        {{M \<in> q7249519_finite_borel_measures.
            integral\<^sup>L M f \<in> U}
          |f U. q7249519_bounded_continuous f \<and> open U}"

theorem prokhorov_s_theorem:
  fixes C :: real
    and u :: "nat \<Rightarrow> real"
    and K :: "nat \<Rightarrow> 'a::t2_space set"
  assumes C_nonnegative: "0 \<le> C"
    and u_nonnegative: "\<And>n. 0 \<le> u n"
    and u_tendsto_zero: "u \<longlonglongrightarrow> 0"
    and K_compact: "\<And>n. compact (K n)"
    and normal_or_monotone:
      "normal_space (euclidean :: 'a topology) \<or> mono K"
  shows
    "compactin q7249519_weak_topology
      {M \<in> q7249519_finite_borel_measures.
        measure M UNIV \<le> C \<and>
        (\<forall>n. measure M (- K n) \<le> u n)}"
  sorry

end
