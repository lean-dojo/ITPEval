(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q1047749 (thousand-theorems__isabelle__Q1047749), "Turán's theorem":
  for a positive number of parts, a finite simple graph is Turán-maximal
  exactly when it is isomorphic to the canonical Turán graph on the same
  number of vertices. This file contains no proof.
*)

theory Q1047749_tur_n_s_theorem
  imports Main
begin

definition q1047749_simple_graph_on ::
    "'v set \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool" where
  "q1047749_simple_graph_on V G \<longleftrightarrow>
    (\<forall>v \<in> V. \<not> G v v) \<and>
    (\<forall>u \<in> V. \<forall>v \<in> V. G u v \<longleftrightarrow> G v u)"

definition q1047749_edge_set_on ::
    "'v set \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> 'v set set" where
  "q1047749_edge_set_on V G =
    (\<lambda>(u, v). {u, v}) ` {(u, v). u \<in> V \<and> v \<in> V \<and> G u v}"

definition q1047749_clique_free_on ::
    "'v set \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "q1047749_clique_free_on V G k \<longleftrightarrow>
    \<not> (\<exists>f :: nat \<Rightarrow> 'v.
      inj_on f {..<k} \<and>
      f ` {..<k} \<subseteq> V \<and>
      (\<forall>i < k. \<forall>j < k. i \<noteq> j \<longrightarrow> G (f i) (f j)))"

definition q1047749_is_turan_maximal_on ::
    "'v set \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "q1047749_is_turan_maximal_on V G r \<longleftrightarrow>
    q1047749_simple_graph_on V G \<and>
    q1047749_clique_free_on V G (r + 1) \<and>
    (\<forall>H :: 'v \<Rightarrow> 'v \<Rightarrow> bool.
      q1047749_simple_graph_on V H \<and>
      q1047749_clique_free_on V H (r + 1)
      \<longrightarrow>
      card (q1047749_edge_set_on V H)
        \<le> card (q1047749_edge_set_on V G))"

definition q1047749_isomorphic_to_turan_on ::
    "'v set \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "q1047749_isomorphic_to_turan_on V G r \<longleftrightarrow>
    (\<exists>f :: 'v \<Rightarrow> nat.
      bij_betw f V {..<card V} \<and>
      (\<forall>u \<in> V. \<forall>v \<in> V.
        G u v \<longleftrightarrow> f u mod r \<noteq> f v mod r))"

theorem q1047749_is_turan_maximal_iff_nonempty_iso_turan:
  fixes V :: "'v set"
    and G :: "'v \<Rightarrow> 'v \<Rightarrow> bool"
    and r :: nat
  assumes "finite V"
    and "q1047749_simple_graph_on V G"
    and "0 < r"
  shows "q1047749_is_turan_maximal_on V G r \<longleftrightarrow>
    q1047749_isomorphic_to_turan_on V G r"
  sorry

end
