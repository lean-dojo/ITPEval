(*
  Statement-only formalization of the thousand-theorems corpus artifact Q595466,
  "Dini's theorem": a monotone family of continuous functions valued in a
  solid-normed lattice-ordered additive group that converges pointwise to a
  continuous limit converges locally uniformly, with possibly empty index and
  domain types represented by carriers. This file contains no proof.
*)

theory Q595466_dini_s_theorem
  imports
    "HOL-Analysis.Uniform_Limit"
    "HOL-Library.Lattice_Algebras"
begin

definition q595466_at_top_on :: "'i::preorder set \<Rightarrow> 'i filter" where
  "q595466_at_top_on I = (INF k\<in>I. principal {j\<in>I. k \<le> j})"

definition q595466_normed_lattice_group ::
    "('g::lattice_ab_group_add \<Rightarrow> real) \<Rightarrow> bool" where
  "q595466_normed_lattice_group normG \<longleftrightarrow>
    (\<forall>x. 0 \<le> normG x) \<and>
    (\<forall>x. normG x = 0 \<longleftrightarrow> x = 0) \<and>
    (\<forall>x. normG (-x) = normG x) \<and>
    (\<forall>x y. normG (x + y) \<le> normG x + normG y) \<and>
    (\<forall>x y. sup x (-x) \<le> sup y (-y) \<longrightarrow> normG x \<le> normG y)"

definition q595466_continuous_on ::
    "'a::topological_space set \<Rightarrow>
      ('g::lattice_ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('a::topological_space \<Rightarrow> 'g) \<Rightarrow> bool" where
  "q595466_continuous_on A normG h \<longleftrightarrow>
    (\<forall>x\<in>A. \<forall>e. 0 < e \<longrightarrow>
      eventually
        (\<lambda>y. y \<in> A \<longrightarrow> normG (- h x + h y) < e)
        (inf (nhds x) (principal A)))"

definition q595466_tendsto_at_top_on ::
    "'i::preorder set \<Rightarrow>
      ('g::lattice_ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('i::preorder \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> bool" where
  "q595466_tendsto_at_top_on I normG u z \<longleftrightarrow>
    (\<forall>e. 0 < e \<longrightarrow>
      eventually
        (\<lambda>i. i \<in> I \<longrightarrow> normG (-z + u i) < e)
        (q595466_at_top_on I))"

definition q595466_tendsto_locally_uniformly_on ::
    "'i::preorder set \<Rightarrow> 'a::topological_space set \<Rightarrow>
      ('g::lattice_ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('i::preorder \<Rightarrow> 'a::topological_space \<Rightarrow> 'g) \<Rightarrow>
      ('a \<Rightarrow> 'g) \<Rightarrow> bool" where
  "q595466_tendsto_locally_uniformly_on I A normG F f \<longleftrightarrow>
    (\<forall>e. 0 < e \<longrightarrow> (\<forall>x\<in>A. \<exists>t.
      eventually (\<lambda>y. y \<in> t) (inf (nhds x) (principal A)) \<and>
      eventually
        (\<lambda>i. i \<in> I \<longrightarrow>
          (\<forall>y\<in>t. y \<in> A \<longrightarrow> normG (- f y + F i y) < e))
        (q595466_at_top_on I)))"

theorem dini_s_theorem:
  fixes I :: "'i::preorder set"
    and A :: "'a::topological_space set"
    and normG :: "'g::lattice_ab_group_add \<Rightarrow> real"
    and F :: "'i::preorder \<Rightarrow> 'a::topological_space \<Rightarrow> 'g"
    and f :: "'a \<Rightarrow> 'g"
  assumes normed_lattice_group:
      "q595466_normed_lattice_group normG"
    and F_continuous:
      "\<And>i. i \<in> I \<Longrightarrow> q595466_continuous_on A normG (F i)"
    and F_monotone:
      "\<And>i j x. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> x \<in> A \<Longrightarrow>
        i \<le> j \<Longrightarrow> F i x \<le> F j x"
    and f_continuous:
      "q595466_continuous_on A normG f"
    and pointwise_tendsto:
      "\<And>x. x \<in> A \<Longrightarrow>
        q595466_tendsto_at_top_on I normG (\<lambda>i. F i x) (f x)"
  shows "q595466_tendsto_locally_uniformly_on I A normG F f"
  sorry

end
