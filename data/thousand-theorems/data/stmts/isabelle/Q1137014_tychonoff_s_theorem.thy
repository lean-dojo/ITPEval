(*
  Statement-only formalization of thousand-theorems corpus artifact Q1137014,
  "Tychonoff's theorem": an arbitrary indexed product of compact subsets of
  topological spaces is compact. This file contains no proof.
*)

theory Q1137014_tychonoff_s_theorem
  imports Main
begin

definition tt_is_topology ::
    "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "tt_is_topology A T \<longleftrightarrow>
    {} \<in> T \<and>
    A \<in> T \<and>
    (\<forall>U \<in> T. U \<subseteq> A) \<and>
    (\<forall>C. C \<subseteq> T \<longrightarrow> \<Union>C \<in> T) \<and>
    (\<forall>U \<in> T. \<forall>V \<in> T. U \<inter> V \<in> T)"

definition tt_compactin ::
    "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "tt_compactin A T K \<longleftrightarrow>
    K \<subseteq> A \<and>
    (\<forall>C. C \<subseteq> T \<longrightarrow> K \<subseteq> \<Union>C \<longrightarrow>
      (\<exists>F \<subseteq> C. finite F \<and> K \<subseteq> \<Union>F))"

definition tt_product_set ::
    "'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow> 'a) set" where
  "tt_product_set I A = {f. \<forall>i \<in> I. f i \<in> A i}"

definition tt_product_open ::
    "('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow> 'a set set) \<Rightarrow>
      'i set \<Rightarrow> ('i \<Rightarrow> 'a) set \<Rightarrow> bool" where
  "tt_product_open A T I U \<longleftrightarrow>
    U \<subseteq> tt_product_set I A \<and>
    (\<forall>x \<in> U. \<exists>J V.
      finite J \<and> J \<subseteq> I \<and>
      (\<forall>i \<in> J. V i \<in> T i) \<and>
      x \<in> tt_product_set I
        (\<lambda>i. if i \<in> J then V i else A i) \<and>
      tt_product_set I
        (\<lambda>i. if i \<in> J then V i else A i) \<subseteq> U)"

definition tt_product_topology ::
    "('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow> 'a set set) \<Rightarrow>
      'i set \<Rightarrow> ('i \<Rightarrow> 'a) set set" where
  "tt_product_topology A T I = {U. tt_product_open A T I U}"

theorem isCompact_pi_infinite:
  fixes A :: "'i \<Rightarrow> 'a set"
    and T :: "'i \<Rightarrow> 'a set set"
    and s :: "'i \<Rightarrow> 'a set"
  assumes "\<And>i. tt_is_topology (A i) (T i)"
    and "\<And>i. tt_compactin (A i) (T i) (s i)"
  shows "tt_compactin
    (tt_product_set UNIV A)
    (tt_product_topology A T UNIV)
    (tt_product_set UNIV s)"
  sorry

end
