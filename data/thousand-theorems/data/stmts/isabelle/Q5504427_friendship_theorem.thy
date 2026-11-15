(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q5504427 (thousand-theorems__isabelle__Q5504427), "Friendship theorem":
  every finite nonempty simple graph in which each pair of distinct vertices
  has exactly one common neighbor has a vertex adjacent to every other vertex.
  This file contains no proof.
*)

theory Q5504427_friendship_theorem
  imports Main
begin

theorem friendship_theorem:
  fixes G :: "('v::finite \<times> 'v) set"
  assumes nonempty: "(UNIV :: 'v set) \<noteq> {}"
    and irreflexive: "\<And>v. (v, v) \<notin> G"
    and symmetric: "\<And>v w. (v, w) \<in> G \<Longrightarrow> (w, v) \<in> G"
    and unique_common_neighbor:
      "\<And>v w. v \<noteq> w \<Longrightarrow>
        card {u. (v, u) \<in> G \<and> (w, u) \<in> G} = 1"
  shows "\<exists>v. \<forall>w. v \<noteq> w \<longrightarrow> (v, w) \<in> G"
  sorry

end
