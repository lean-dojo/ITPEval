(*
  Statement-only formalization of the thousand-theorems corpus artifact Q643826,
  "Slutsky's theorem": composing a continuous function with random variables
  converging respectively in distribution and in probability to a constant
  preserves convergence in distribution. This file contains no proof.
*)

theory Q643826_slutsky_s_theorem
  imports
    "HOL-Analysis.Bochner_Integration"
    "HOL-Analysis.Complete_Measure"
    "HOL-Analysis.Infinite_Sum"
begin

definition q643826_probability_measure :: "'a measure \<Rightarrow> bool"
  where
    "q643826_probability_measure M \<longleftrightarrow>
      space M = UNIV \<and> emeasure M UNIV = 1"

definition q643826_seminormed_add_comm_group ::
    "('a::{ab_group_add, second_countable_topology} \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q643826_seminormed_add_comm_group normA \<longleftrightarrow>
      (\<forall>x. 0 \<le> normA x) \<and>
      normA 0 = 0 \<and>
      (\<forall>x. normA (-x) = normA x) \<and>
      (\<forall>x y. normA (x + y) \<le> normA x + normA y) \<and>
      (\<forall>U. open U \<longleftrightarrow>
        (\<forall>x\<in>U. \<exists>e>0. \<forall>y. normA (-x + y) < e \<longrightarrow> y \<in> U))"

definition q643826_ae_measurable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) \<Rightarrow> bool"
  where
    "q643826_ae_measurable M f \<longleftrightarrow>
      (\<exists>f'. f' \<in> borel_measurable M \<and> (AE x in M. f x = f' x))"

definition q643826_has_law ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) \<Rightarrow>
      'b measure \<Rightarrow> bool"
  where
    "q643826_has_law M f law \<longleftrightarrow>
      (\<exists>f'. f' \<in> borel_measurable M \<and>
        (AE x in M. f x = f' x) \<and> distr M borel f' = law)"

definition q643826_weak_convergence ::
    "'i filter \<Rightarrow> ('i \<Rightarrow> 'a::topological_space measure) \<Rightarrow>
      'a measure \<Rightarrow> bool"
  where
    "q643826_weak_convergence l laws limit_law \<longleftrightarrow>
      (\<forall>i. q643826_probability_measure (laws i)) \<and>
      q643826_probability_measure limit_law \<and>
      (\<forall>i. sets (laws i) = sets limit_law) \<and>
      sets borel \<subseteq> sets limit_law \<and>
      (\<forall>f :: 'a \<Rightarrow> real.
        bounded (range f) \<and> continuous_on UNIV f \<longrightarrow>
        filterlim
          (\<lambda>i. integral\<^sup>L (laws i) f)
          (nhds (integral\<^sup>L limit_law f))
          l)"

definition q643826_tendsto_in_distribution ::
    "'i filter \<Rightarrow> 'a measure \<Rightarrow>
      ('i \<Rightarrow> 'a \<Rightarrow> 'b::topological_space) \<Rightarrow>
      'c measure \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> bool"
  where
    "q643826_tendsto_in_distribution l M X N Z \<longleftrightarrow>
      q643826_probability_measure M \<and>
      q643826_probability_measure N \<and>
      (\<forall>i. q643826_ae_measurable M (X i)) \<and>
      q643826_ae_measurable N Z \<and>
      (\<exists>laws limit_law.
        (\<forall>i. q643826_has_law M (X i) (laws i)) \<and>
        q643826_has_law N Z limit_law \<and>
        q643826_weak_convergence l laws limit_law)"

definition q643826_tendsto_in_measure_const ::
    "'i filter \<Rightarrow> 'a measure \<Rightarrow>
      ('i \<Rightarrow> 'a \<Rightarrow> 'b::{ab_group_add, second_countable_topology}) \<Rightarrow>
      ('b \<Rightarrow> real) \<Rightarrow> 'b \<Rightarrow> bool"
  where
    "q643826_tendsto_in_measure_const l M Y normB c \<longleftrightarrow>
      (\<forall>e>0.
        filterlim
          (\<lambda>i. outer_measure_of M
            {\<omega> \<in> space M. e \<le> normB (-c + Y i \<omega>)})
          (nhds 0)
          l)"

theorem slutsky_s_theorem:
  fixes l :: "'i filter"
    and M :: "'a measure"
    and N :: "'c measure"
    and X :: "'i \<Rightarrow> 'a \<Rightarrow> 'e::{ab_group_add, second_countable_topology}"
    and Y :: "'i \<Rightarrow> 'a \<Rightarrow> 'd::{ab_group_add, second_countable_topology}"
    and Z :: "'c \<Rightarrow> 'e"
    and c :: "'d"
    and g :: "'e \<times> 'd \<Rightarrow> 'f::topological_space"
    and normE :: "'e \<Rightarrow> real"
    and normD :: "'d \<Rightarrow> real"
  assumes E_seminormed:
      "q643826_seminormed_add_comm_group normE"
    and D_seminormed:
      "q643826_seminormed_add_comm_group normD"
    and countably_generated:
      "countably_generated_filter l"
    and X_tendsto:
      "q643826_tendsto_in_distribution l M X N Z"
    and Y_tendsto:
      "q643826_tendsto_in_measure_const l M Y normD c"
    and Y_ae_measurable:
      "\<And>i. q643826_ae_measurable M (Y i)"
    and g_continuous:
      "continuous_on UNIV g"
  shows
      "q643826_tendsto_in_distribution l M
        (\<lambda>i \<omega>. g (X i \<omega>, Y i \<omega>))
        N
        (\<lambda>\<omega>. g (Z \<omega>, c))"
  sorry

end
