theory vstte12_bfs_BFS_fill_nextqtvc
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
theorem fill_next'vc:
  fixes s :: "vertex"
  fixes t :: "vertex"
  fixes visited :: "set"
  fixes current :: "set"
  fixes "next" :: "set"
  fixes d :: "int"
  fixes v :: "vertex"
  fixes acc :: "set"
  assumes fact0: "inv s t (to_fset visited) (to_fset current) (to_fset next) d"
  assumes fact1: "shortest_path s v d"
  assumes fact2: "\<forall>(x :: vertex). \<not>x = v \<longrightarrow> closure (to_fset visited) (to_fset current) (to_fset next) x"
  assumes fact3: "to_fset acc = succ v"
  shows "inv s t (to_fset visited) (to_fset current) (to_fset next) d"
  and "to_fset acc |\<subseteq>| succ v"
  and "succ v |-| to_fset acc |\<subseteq>| to_fset visited"
  and "\<forall>(x :: vertex). \<not>x = v \<longrightarrow> closure (to_fset visited) (to_fset current) (to_fset next) x"
  and "\<forall>(acc1 :: set) (next1 :: set) (visited1 :: set). inv s t (to_fset visited1) (to_fset current) (to_fset next1) d \<and> to_fset acc1 |\<subseteq>| succ v \<and> succ v |-| to_fset acc1 |\<subseteq>| to_fset visited1 \<and> (\<forall>(x :: vertex). \<not>x = v \<longrightarrow> closure (to_fset visited1) (to_fset current) (to_fset next1) x) \<longrightarrow> (if \<not>to_fset acc1 = fempty then \<not>to_fset acc1 = fempty \<and> (\<forall>(acc2 :: set). let w :: vertex = choose1 acc1 in w |\<in>| to_fset acc1 \<and> to_fset acc2 = fset_remove w (to_fset acc1) \<longrightarrow> (if \<not>w |\<in>| to_fset visited1 then \<forall>(visited2 :: set). to_fset visited2 = finsert w (to_fset visited1) \<and> (if w |\<in>| to_fset visited1 then fcard (to_fset visited2) = fcard (to_fset visited1) else int (fcard (to_fset visited2)) = int (fcard (to_fset visited1)) + (1 :: int)) \<longrightarrow> (\<forall>(next2 :: set). to_fset next2 = finsert w (to_fset next1) \<and> (if w |\<in>| to_fset next1 then fcard (to_fset next2) = fcard (to_fset next1) else int (fcard (to_fset next2)) = int (fcard (to_fset next1)) + (1 :: int)) \<longrightarrow> ((0 :: int) \<le> int (fcard (to_fset acc1)) \<and> fcard (to_fset acc2) < fcard (to_fset acc1)) \<and> inv s t (to_fset visited2) (to_fset current) (to_fset next2) d \<and> to_fset acc2 |\<subseteq>| succ v \<and> succ v |-| to_fset acc2 |\<subseteq>| to_fset visited2 \<and> (\<forall>(x :: vertex). \<not>x = v \<longrightarrow> closure (to_fset visited2) (to_fset current) (to_fset next2) x)) else ((0 :: int) \<le> int (fcard (to_fset acc1)) \<and> fcard (to_fset acc2) < fcard (to_fset acc1)) \<and> inv s t (to_fset visited1) (to_fset current) (to_fset next1) d \<and> to_fset acc2 |\<subseteq>| succ v \<and> succ v |-| to_fset acc2 |\<subseteq>| to_fset visited1 \<and> (\<forall>(x :: vertex). \<not>x = v \<longrightarrow> closure (to_fset visited1) (to_fset current) (to_fset next1) x))) else inv s t (to_fset visited1) (to_fset current) (to_fset next1) d \<and> succ v |\<subseteq>| to_fset visited1 \<and> (\<forall>(x :: vertex). closure (to_fset visited1) (to_fset current) (to_fset next1) x))"
  sorry
end
