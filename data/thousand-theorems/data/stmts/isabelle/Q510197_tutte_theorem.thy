(*
  Statement-only formalization of thousand-theorems corpus artifact Q510197
  (thousand-theorems__isabelle__Q510197), "Tutte theorem": a finite simple
  graph has a perfect matching exactly when deleting any vertex subset leaves
  at most that many odd connected components. This file contains no proof.
*)

theory Q510197_tutte_theorem
  imports Main
begin

definition q510197_simple_graph ::
    "('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool" where
  "q510197_simple_graph G \<longleftrightarrow>
    (\<forall>v. \<not> G v v) \<and>
    (\<forall>u v. G u v \<longleftrightarrow> G v u)"

definition q510197_perfect_matching ::
    "('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow>
      ('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool" where
  "q510197_perfect_matching G M \<longleftrightarrow>
    (\<forall>u v. M u v \<longrightarrow> G u v) \<and>
    (\<forall>u v. M u v \<longleftrightarrow> M v u) \<and>
    (\<forall>v. \<not> M v v) \<and>
    (\<forall>v. \<exists>!w. M v w)"

definition q510197_reachable_after_deleting ::
    "('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> 'v set \<Rightarrow>
      'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "q510197_reachable_after_deleting G U x y \<longleftrightarrow>
    x \<notin> U \<and> y \<notin> U \<and>
    rtranclp (\<lambda>a b. a \<notin> U \<and> b \<notin> U \<and> G a b) x y"

definition q510197_component_after_deleting ::
    "('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> 'v set \<Rightarrow>
      'v \<Rightarrow> 'v set" where
  "q510197_component_after_deleting G U v =
    {w. q510197_reachable_after_deleting G U v w}"

definition q510197_odd_components_after_deleting ::
    "('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> 'v set \<Rightarrow>
      'v set set" where
  "q510197_odd_components_after_deleting G U =
    {C. \<exists>v. v \<notin> U \<and>
      C = q510197_component_after_deleting G U v \<and>
      odd (card C)}"

definition q510197_is_tutte_violator ::
    "('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> 'v set \<Rightarrow> bool" where
  "q510197_is_tutte_violator G U \<longleftrightarrow>
    card U < card (q510197_odd_components_after_deleting G U)"

theorem q510197_tutte:
  fixes G :: "'v::finite \<Rightarrow> 'v \<Rightarrow> bool"
  assumes simple_graph: "q510197_simple_graph G"
  shows "(\<exists>M. q510197_perfect_matching G M) \<longleftrightarrow>
    (\<forall>U. \<not> q510197_is_tutte_violator G U)"
  sorry

end
