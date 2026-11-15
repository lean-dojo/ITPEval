(*
  Statement-only formalization of thousand-theorems corpus artifact Q1243340
  (thousand-theorems__isabelle__Q1243340), "Birkhoff–Von Neumann theorem":
  over any linearly ordered field and any finite carrier, including the empty
  carrier, the doubly stochastic matrices are exactly the convex hull of the
  permutation matrices. This file contains no proof.
*)

theory Q1243340_birkhoff_von_neumann_theorem
  imports Main
begin

definition q1243340_doubly_stochastic ::
    "'i set \<Rightarrow> ('i \<Rightarrow> 'i \<Rightarrow> 'a::linordered_field) set"
  where
  "q1243340_doubly_stochastic I =
    {M. (\<forall>i j. M i j \<noteq> 0 \<longrightarrow> i \<in> I \<and> j \<in> I) \<and>
      (\<forall>i\<in>I. \<forall>j\<in>I. 0 \<le> M i j) \<and>
      (\<forall>i\<in>I. (\<Sum>j\<in>I. M i j) = 1) \<and>
      (\<forall>j\<in>I. (\<Sum>i\<in>I. M i j) = 1)}"

definition q1243340_permutation_matrices ::
    "'i set \<Rightarrow> ('i \<Rightarrow> 'i \<Rightarrow> 'a::linordered_field) set"
  where
  "q1243340_permutation_matrices I =
    {P. \<exists>\<sigma> :: 'i \<Rightarrow> 'i.
      bij_betw \<sigma> I I \<and>
      P = (\<lambda>i j. if i \<in> I \<and> j \<in> I \<and> \<sigma> i = j then 1 else 0)}"

definition q1243340_convex_hull_matrix ::
    "('i \<Rightarrow> 'i \<Rightarrow> 'a::linordered_field) set
      \<Rightarrow> ('i \<Rightarrow> 'i \<Rightarrow> 'a) set" where
  "q1243340_convex_hull_matrix S =
    {M. \<exists>w :: ('i \<Rightarrow> 'i \<Rightarrow> 'a) \<Rightarrow> 'a.
      finite {P. w P \<noteq> 0} \<and>
      {P. w P \<noteq> 0} \<subseteq> S \<and>
      (\<forall>P. 0 \<le> w P) \<and>
      (\<Sum>P\<in>{P. w P \<noteq> 0}. w P) = 1 \<and>
      M = (\<lambda>i j. \<Sum>P\<in>{P. w P \<noteq> 0}. w P * P i j)}"

theorem doublyStochastic_eq_convexHull_permMatrix:
  fixes I :: "'i set"
  assumes finite_I: "finite I"
  shows "(q1243340_doubly_stochastic I ::
      ('i \<Rightarrow> 'i \<Rightarrow> 'a::linordered_field) set) =
    q1243340_convex_hull_matrix (q1243340_permutation_matrices I)"
  sorry

end
