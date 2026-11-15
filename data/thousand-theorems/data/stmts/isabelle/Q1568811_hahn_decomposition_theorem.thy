(*
  Statement-only formalization of the thousand-theorems corpus artifact Q1568811,
  "Hahn decomposition theorem": every signed measure on an arbitrary measurable
  space admits complementary measurable positive and negative sets. This file
  contains no proof.
*)

theory Q1568811_hahn_decomposition_theorem
  imports "HOL-Analysis.Measure_Space"
begin

definition q1568811_sigma_algebra :: "'a set set \<Rightarrow> bool" where
  "q1568811_sigma_algebra S \<longleftrightarrow>
    {} \<in> S \<and>
    (\<forall>A \<in> S. - A \<in> S) \<and>
    (\<forall>A :: nat \<Rightarrow> 'a set.
      (\<forall>n. A n \<in> S) \<longrightarrow> (\<Union>n. A n) \<in> S)"

definition q1568811_signed_measure ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> bool" where
  "q1568811_signed_measure S s \<longleftrightarrow>
    q1568811_sigma_algebra S \<and>
    s {} = 0 \<and>
    (\<forall>A. A \<notin> S \<longrightarrow> s A = 0) \<and>
    (\<forall>A :: nat \<Rightarrow> 'a set.
      (\<forall>n. A n \<in> S) \<longrightarrow>
      (\<forall>m n. m \<noteq> n \<longrightarrow> A m \<inter> A n = {}) \<longrightarrow>
      (\<lambda>n. s (A n)) sums s (\<Union>n. A n))"

definition q1568811_positive_set ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q1568811_positive_set S s P \<longleftrightarrow>
    (\<forall>A \<in> S. A \<subseteq> P \<longrightarrow> 0 \<le> s A)"

definition q1568811_negative_set ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q1568811_negative_set S s N \<longleftrightarrow>
    (\<forall>A \<in> S. A \<subseteq> N \<longrightarrow> s A \<le> 0)"

definition q1568811_complementary :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q1568811_complementary P N \<longleftrightarrow>
    P \<inter> N = {} \<and> P \<union> N = UNIV"

theorem hahn_decomposition_theorem:
  fixes S :: "'a set set"
    and s :: "'a set \<Rightarrow> real"
  assumes "q1568811_signed_measure S s"
  shows "\<exists>P N.
    P \<in> S \<and>
    q1568811_positive_set S s P \<and>
    N \<in> S \<and>
    q1568811_negative_set S s N \<and>
    q1568811_complementary P N"
  sorry

end
