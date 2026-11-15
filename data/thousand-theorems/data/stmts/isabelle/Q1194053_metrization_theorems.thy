(*
  Statement-only formalization of thousand-theorems corpus artifact Q1194053,
  "Metrization theorems": Urysohn's metrization theorem states that every T3,
  second-countable topology is induced by a metric. This file contains no proof.
*)

theory Q1194053_metrization_theorems
  imports "HOL.Real"
begin

definition mt_is_topology :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "mt_is_topology A T \<longleftrightarrow>
    T \<subseteq> Pow A \<and>
    {} \<in> T \<and>
    A \<in> T \<and>
    (\<forall>K. K \<subseteq> T \<longrightarrow> \<Union>K \<in> T) \<and>
    (\<forall>U \<in> T. \<forall>V \<in> T. U \<inter> V \<in> T)"

definition mt_is_t3 :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "mt_is_t3 A T \<longleftrightarrow>
    (\<forall>x \<in> A. \<forall>y \<in> A. x \<noteq> y \<longrightarrow>
      (\<exists>U \<in> T. \<exists>V \<in> T.
        x \<in> U \<and> y \<in> V \<and> U \<inter> V = {})) \<and>
    (\<forall>C \<subseteq> A. A - C \<in> T \<longrightarrow>
      (\<forall>x \<in> A. x \<notin> C \<longrightarrow>
      (\<exists>U \<in> T. \<exists>V \<in> T.
        x \<in> U \<and> C \<subseteq> V \<and> U \<inter> V = {})))"

definition mt_is_second_countable :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "mt_is_second_countable A T \<longleftrightarrow>
    (\<exists>b :: nat \<Rightarrow> 'a set. (\<forall>n. b n \<in> T) \<and>
      (\<forall>U \<in> T. \<forall>x \<in> U.
        \<exists>n. x \<in> b n \<and> b n \<subseteq> U))"

definition mt_is_metric_on ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "mt_is_metric_on A d \<longleftrightarrow>
    (\<forall>x \<in> A. \<forall>y \<in> A. 0 \<le> d x y) \<and>
    (\<forall>x \<in> A. \<forall>y \<in> A. d x y = 0 \<longleftrightarrow> x = y) \<and>
    (\<forall>x \<in> A. \<forall>y \<in> A. d x y = d y x) \<and>
    (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A.
      d x z \<le> d x y + d y z)"

definition mt_metric_open_family ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set set" where
  "mt_metric_open_family A d =
    {U. U \<subseteq> A \<and>
      (\<forall>x \<in> U. \<exists>r>0. \<forall>y \<in> A. d x y < r \<longrightarrow> y \<in> U)}"

definition mt_is_metrizable :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "mt_is_metrizable A T \<longleftrightarrow>
    (\<exists>d :: 'a \<Rightarrow> 'a \<Rightarrow> real.
      mt_is_metric_on A d \<and> T = mt_metric_open_family A d)"

theorem urysohn_metrization:
  fixes A :: "'a set"
    and T :: "'a set set"
  assumes "mt_is_topology A T"
    and "mt_is_t3 A T"
    and "mt_is_second_countable A T"
  shows "mt_is_metrizable A T"
  sorry

end
