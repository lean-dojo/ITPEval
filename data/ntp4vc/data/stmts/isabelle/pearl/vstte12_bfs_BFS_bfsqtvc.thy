theory vstte12_bfs_BFS_bfsqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "./vstte12_bfs_Graph"
begin
typedecl  set
consts to_fset :: "set \<Rightarrow> vertex fset"
consts choose1 :: "set \<Rightarrow> vertex"
axiomatization where choose'spec:   "choose1 s |\<in>| to_fset s"
 if "\<not>to_fset s = fempty"
  for s :: "set"
definition inv :: "vertex \<Rightarrow> vertex \<Rightarrow> vertex fset \<Rightarrow> vertex fset \<Rightarrow> vertex fset \<Rightarrow> int \<Rightarrow> _"
  where "inv s t visited current next d \<longleftrightarrow> current |\<subseteq>| visited \<and> (\<forall>(x :: vertex). x |\<in>| current \<longrightarrow> shortest_path s x d) \<and> next |\<subseteq>| visited \<and> (\<forall>(x :: vertex). x |\<in>| next \<longrightarrow> shortest_path s x (d + (1 :: int))) \<and> (\<forall>(x :: vertex) (m :: int). path s x m \<longrightarrow> m \<le> d \<longrightarrow> x |\<in>| visited) \<and> (\<forall>(x :: vertex). x |\<in>| visited \<longrightarrow> (\<exists>(m :: int). path s x m \<and> m \<le> d + (1 :: int))) \<and> (\<forall>(x :: vertex). shortest_path s x (d + (1 :: int)) \<longrightarrow> x |\<in>| next \<or> \<not>x |\<in>| visited) \<and> (t |\<in>| visited \<longrightarrow> t |\<in>| current \<or> t |\<in>| next)" for s t visited current "next" d
definition closure :: "vertex fset \<Rightarrow> vertex fset \<Rightarrow> vertex fset \<Rightarrow> vertex \<Rightarrow> _"
  where "closure visited current next x \<longleftrightarrow> x |\<in>| visited \<longrightarrow> \<not>x |\<in>| current \<longrightarrow> \<not>x |\<in>| next \<longrightarrow> (\<forall>(y :: vertex). y |\<in>| succ x \<longrightarrow> y |\<in>| visited)" for visited current "next" x
theorem bfs'vc:
  fixes visited :: "set"
  fixes o1 :: "set"
  fixes o2 :: "set"
  fixes visited1 :: "set"
  fixes s :: "vertex"
  fixes current :: "set"
  fixes t :: "vertex"
  assumes fact0: "to_fset visited = fempty"
  assumes fact1: "int (fcard (to_fset visited)) = (0 :: int)"
  assumes fact2: "to_fset o1 = fempty"
  assumes fact3: "int (fcard (to_fset o1)) = (0 :: int)"
  assumes fact4: "to_fset o2 = fempty"
  assumes fact5: "int (fcard (to_fset o2)) = (0 :: int)"
  assumes fact6: "to_fset visited1 = finsert s (to_fset visited)"
  assumes fact7: "if s |\<in>| to_fset visited then fcard (to_fset visited1) = fcard (to_fset visited) else int (fcard (to_fset visited1)) = int (fcard (to_fset visited)) + (1 :: int)"
  assumes fact8: "to_fset current = finsert s (to_fset o1)"
  assumes fact9: "if s |\<in>| to_fset o1 then fcard (to_fset current) = fcard (to_fset o1) else int (fcard (to_fset current)) = int (fcard (to_fset o1)) + (1 :: int)"
  shows "inv s t (to_fset visited1) (to_fset current) (to_fset o2) (0 :: int)"
  and "to_fset current = fempty \<longrightarrow> to_fset o2 = fempty"
  and "\<forall>(x :: vertex). closure (to_fset visited1) (to_fset current) (to_fset o2) x"
  and "(0 :: int) \<le> (0 :: int)"
  and "\<forall>(d :: int) (next :: set) (current1 :: set) (visited2 :: set). inv s t (to_fset visited2) (to_fset current1) (to_fset next) d \<and> (to_fset current1 = fempty \<longrightarrow> to_fset next = fempty) \<and> (\<forall>(x :: vertex). closure (to_fset visited2) (to_fset current1) (to_fset next) x) \<and> (0 :: int) \<le> d \<longrightarrow> (if \<not>to_fset current1 = fempty then \<not>to_fset current1 = fempty \<and> (\<forall>(current2 :: set). let v :: vertex = choose1 current1 in v |\<in>| to_fset current1 \<and> to_fset current2 = fset_remove v (to_fset current1) \<longrightarrow> (eq v t \<longleftrightarrow> v = t) \<longrightarrow> (if eq v t then shortest_path s t d else (inv s t (to_fset visited2) (to_fset current2) (to_fset next) d \<and> shortest_path s v d \<and> (\<forall>(x :: vertex). \<not>x = v \<longrightarrow> closure (to_fset visited2) (to_fset current2) (to_fset next) x)) \<and> (\<forall>(next1 :: set) (visited3 :: set). inv s t (to_fset visited3) (to_fset current2) (to_fset next1) d \<and> succ v |\<subseteq>| to_fset visited3 \<and> (\<forall>(x :: vertex). closure (to_fset visited3) (to_fset current2) (to_fset next1) x) \<longrightarrow> (if to_fset current2 = fempty then \<forall>(o3 :: set). to_fset o3 = fempty \<and> int (fcard (to_fset o3)) = (0 :: int) \<longrightarrow> inv s t (to_fset visited3) (to_fset next1) (to_fset o3) (d + (1 :: int)) \<and> (to_fset next1 = fempty \<longrightarrow> to_fset o3 = fempty) \<and> (\<forall>(x :: vertex). closure (to_fset visited3) (to_fset next1) (to_fset o3) x) \<and> (0 :: int) \<le> d + (1 :: int) else inv s t (to_fset visited3) (to_fset current2) (to_fset next1) d \<and> (to_fset current2 = fempty \<longrightarrow> to_fset next1 = fempty) \<and> (\<forall>(x :: vertex). closure (to_fset visited3) (to_fset current2) (to_fset next1) x) \<and> (0 :: int) \<le> d)))) else \<forall>(d1 :: int). \<not>path s t d1)"
  sorry
end
