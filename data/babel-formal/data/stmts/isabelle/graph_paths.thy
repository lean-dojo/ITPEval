theory graph_paths
  imports Main
begin

inductive Path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for E :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  Pnil:  "Path E v v"
| Pstep: "Path E u v \<Longrightarrow> E v w \<Longrightarrow> Path E u w"

definition undirected :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "undirected E \<equiv> \<forall>x y. E x y \<longrightarrow> E y x"

definition Erev :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "Erev E x y \<equiv> E y x"

lemma path_refl: "Path E v v"
  sorry

lemma path_trans:
  assumes "Path E u v" "Path E v w" shows "Path E u w"
  sorry

lemma trans: "Path E u v \<Longrightarrow> Path E v w \<Longrightarrow> Path E u w"
  sorry


lemma edge_path: "E u v \<Longrightarrow> Path E u v"
  sorry

lemma concat_edge_right: "Path E u v \<Longrightarrow> E v w \<Longrightarrow> Path E u w"
  sorry

lemma concat: "Path E u v \<Longrightarrow> Path E v w \<Longrightarrow> Path E u w"
  sorry

lemma concat_edge_left: "E u v \<Longrightarrow> Path E v w \<Longrightarrow> Path E u w"
  sorry

lemma concat3:
  "Path E u v \<Longrightarrow> Path E v w \<Longrightarrow> Path E w t \<Longrightarrow> Path E u t"
  sorry


lemma reverse_cons:
  assumes hE: "undirected E" and e: "E m v" and ih: "Path E m u"
  shows "Path E v u"
  sorry

lemma reverse_path:
  assumes hE: "undirected E" and p: "Path E u v"
  shows "Path E v u"
  sorry


lemma reverse_cons_Erev:
  assumes e: "E m v" and ih: "Path (Erev E) m u"
  shows "Path (Erev E) v u"
  sorry

lemma reverse_in_Erev:
  assumes p: "Path E u v"
  shows "Path (Erev E) v u"
  sorry

lemma cycle_refl:
  "Path E v w \<Longrightarrow> Path E w v \<Longrightarrow> Path E v v"
  sorry

end
