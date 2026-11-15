theory dijkstra_DijkstraShortestPath_shortest_path_codeqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const"
begin
typedecl  vertex
typedecl  set
consts to_fset :: "set \<Rightarrow> vertex fset"
consts choose1 :: "set \<Rightarrow> vertex"
axiomatization where choose'spec:   "choose1 s |\<in>| to_fset s"
 if "\<not>to_fset s = fempty"
  for s :: "set"
typedecl 'a t
consts contents :: "'a t \<Rightarrow> vertex \<Rightarrow> 'a"
consts create :: "'a \<Rightarrow> 'a t"
axiomatization where create'spec:   "contents (create x) = (const :: 'a \<Rightarrow> vertex \<Rightarrow> 'a) x"
  for x :: "'a"
consts mixfix_lbrb :: "'a t \<Rightarrow> vertex \<Rightarrow> 'a"
axiomatization where mixfix_lbrb'spec:   "mixfix_lbrb m k = contents m k"
  for m :: "'a t"
  and k :: "vertex"
consts mixfix_lblsmnrb :: "'a t \<Rightarrow> vertex \<Rightarrow> 'a \<Rightarrow> 'a t"
axiomatization where mixfix_lblsmnrb'spec:   "contents (mixfix_lblsmnrb m k v) = (contents m)(k := v)"
  for m :: "'a t"
  and k :: "vertex"
  and v :: "'a"
consts v :: "vertex fset"
consts g_succ :: "vertex \<Rightarrow> vertex fset"
axiomatization where g_succ'spec:   "g_succ x_x |\<subseteq>| v"
  for x_x :: "vertex"
consts weight :: "vertex \<Rightarrow> vertex \<Rightarrow> int"
axiomatization where weight'spec:   "(0 :: int) \<le> weight x x_1"
  for x :: "vertex"
  and x_1 :: "vertex"
definition min :: "vertex \<Rightarrow> set \<Rightarrow> int t \<Rightarrow> _"
  where "min m q d \<longleftrightarrow> m |\<in>| to_fset q \<and> (\<forall>(x :: vertex). x |\<in>| to_fset q \<longrightarrow> mixfix_lbrb d m \<le> mixfix_lbrb d x)" for m q d
inductive path :: "vertex \<Rightarrow> vertex \<Rightarrow> int \<Rightarrow> bool" where
   Path_nil: "path x x (0 :: int)" for x :: "vertex"
 | Path_cons: "path x y d \<Longrightarrow> z |\<in>| g_succ y \<Longrightarrow> path x z (d + weight y z)" for x :: "vertex" and y :: "vertex" and d :: "int" and z :: "vertex"
definition shortest_path :: "vertex \<Rightarrow> vertex \<Rightarrow> int \<Rightarrow> _"
  where "shortest_path x y d \<longleftrightarrow> path x y d \<and> (\<forall>(d' :: int). path x y d' \<longrightarrow> d \<le> d')" for x y d
definition inv_src :: "vertex \<Rightarrow> set \<Rightarrow> set \<Rightarrow> _"
  where "inv_src src s q \<longleftrightarrow> src |\<in>| to_fset s \<or> src |\<in>| to_fset q" for src s q
definition inv :: "vertex \<Rightarrow> set \<Rightarrow> set \<Rightarrow> int t \<Rightarrow> _"
  where "inv src s q d \<longleftrightarrow> inv_src src s q \<and> mixfix_lbrb d src = (0 :: int) \<and> to_fset s |\<subseteq>| v \<and> to_fset q |\<subseteq>| v \<and> (\<forall>(v1 :: vertex). v1 |\<in>| to_fset q \<longrightarrow> \<not>v1 |\<in>| to_fset s) \<and> (\<forall>(v1 :: vertex). v1 |\<in>| to_fset s \<longrightarrow> shortest_path src v1 (mixfix_lbrb d v1)) \<and> (\<forall>(v1 :: vertex). v1 |\<in>| to_fset q \<longrightarrow> path src v1 (mixfix_lbrb d v1))" for src s q d
definition inv_succ :: "vertex \<Rightarrow> set \<Rightarrow> set \<Rightarrow> int t \<Rightarrow> _"
  where "inv_succ x_src s q d \<longleftrightarrow> (\<forall>(x :: vertex). x |\<in>| to_fset s \<longrightarrow> (\<forall>(y :: vertex). y |\<in>| g_succ x \<longrightarrow> (y |\<in>| to_fset s \<or> y |\<in>| to_fset q) \<and> mixfix_lbrb d y \<le> mixfix_lbrb d x + weight x y))" for x_src s q d
definition inv_succ2 :: "vertex \<Rightarrow> set \<Rightarrow> set \<Rightarrow> int t \<Rightarrow> vertex \<Rightarrow> set \<Rightarrow> _"
  where "inv_succ2 x_src s q d u su \<longleftrightarrow> (\<forall>(x :: vertex). x |\<in>| to_fset s \<longrightarrow> (\<forall>(y :: vertex). y |\<in>| g_succ x \<longrightarrow> \<not>x = u \<or> x = u \<and> \<not>y |\<in>| to_fset su \<longrightarrow> (y |\<in>| to_fset s \<or> y |\<in>| to_fset q) \<and> mixfix_lbrb d y \<le> mixfix_lbrb d x + weight x y))" for x_src s q d u su
theorem shortest_path_code'vc:
  fixes src :: "vertex"
  fixes dst :: "vertex"
  fixes visited :: "set"
  fixes q :: "set"
  fixes d :: "int t"
  assumes fact0: "src |\<in>| v"
  assumes fact1: "dst |\<in>| v"
  assumes fact2: "to_fset visited = fempty"
  assumes fact3: "to_fset q = finsert src fempty"
  shows "inv src visited q (mixfix_lblsmnrb d src (0 :: int))"
  and "inv_succ src visited q (mixfix_lblsmnrb d src (0 :: int))"
  and "\<forall>(m :: vertex). min m q (mixfix_lblsmnrb d src (0 :: int)) \<longrightarrow> (\<forall>(x :: vertex) (dx :: int). path src x dx \<longrightarrow> dx < mixfix_lbrb (mixfix_lblsmnrb d src (0 :: int)) m \<longrightarrow> x |\<in>| to_fset visited)"
  and "\<forall>(q1 :: set) (d1 :: int t) (visited1 :: set). inv src visited1 q1 d1 \<and> inv_succ src visited1 q1 d1 \<and> (\<forall>(m :: vertex). min m q1 d1 \<longrightarrow> (\<forall>(x :: vertex) (dx :: int). path src x dx \<longrightarrow> dx < mixfix_lbrb d1 m \<longrightarrow> x |\<in>| to_fset visited1)) \<longrightarrow> (if \<not>to_fset q1 = fempty then \<not>to_fset q1 = fempty \<and> (\<forall>(q2 :: set) (u :: vertex). min u q1 d1 \<and> to_fset q2 = fset_remove u (to_fset q1) \<longrightarrow> (\<forall>(visited2 :: set). to_fset visited2 = finsert u (to_fset visited1) \<and> (if u |\<in>| to_fset visited1 then fcard (to_fset visited2) = fcard (to_fset visited1) else int (fcard (to_fset visited2)) = int (fcard (to_fset visited1)) + (1 :: int)) \<longrightarrow> (\<forall>(su :: set). to_fset su = g_succ u \<longrightarrow> (to_fset su |\<subseteq>| g_succ u \<and> inv src visited2 q2 d1 \<and> inv_succ2 src visited2 q2 d1 u su) \<and> (\<forall>(su1 :: set) (q3 :: set) (d2 :: int t). to_fset su1 |\<subseteq>| g_succ u \<and> inv src visited2 q3 d2 \<and> inv_succ2 src visited2 q3 d2 u su1 \<longrightarrow> (if \<not>to_fset su1 = fempty then \<not>to_fset su1 = fempty \<and> (\<forall>(su2 :: set). let v1 :: vertex = choose1 su1 in v1 |\<in>| to_fset su1 \<and> to_fset su2 = fset_remove v1 (to_fset su1) \<longrightarrow> (\<forall>(q4 :: set) (d3 :: int t). v1 |\<in>| to_fset visited2 \<and> q4 = q3 \<and> d3 = d2 \<or> v1 |\<in>| to_fset q4 \<and> mixfix_lbrb d3 v1 \<le> mixfix_lbrb d3 u + weight u v1 \<and> q4 = q3 \<and> d3 = d2 \<or> v1 |\<in>| to_fset q4 \<and> mixfix_lbrb d2 u + weight u v1 < mixfix_lbrb d2 v1 \<and> q4 = q3 \<and> d3 = mixfix_lblsmnrb d2 v1 (mixfix_lbrb d2 u + weight u v1) \<or> \<not>v1 |\<in>| to_fset visited2 \<and> \<not>v1 |\<in>| to_fset q3 \<and> to_fset q4 = finsert v1 (to_fset q3) \<and> d3 = mixfix_lblsmnrb d2 v1 (mixfix_lbrb d2 u + weight u v1) \<longrightarrow> ((0 :: int) \<le> int (fcard (to_fset su1)) \<and> fcard (to_fset su2) < fcard (to_fset su1)) \<and> to_fset su2 |\<subseteq>| g_succ u \<and> inv src visited2 q4 d3 \<and> inv_succ2 src visited2 q4 d3 u su2)) else ((0 :: int) \<le> int (fcard v) - int (fcard (to_fset visited1)) \<and> int (fcard v) - int (fcard (to_fset visited2)) < int (fcard v) - int (fcard (to_fset visited1))) \<and> inv src visited2 q3 d2 \<and> inv_succ src visited2 q3 d2 \<and> (\<forall>(m :: vertex). min m q3 d2 \<longrightarrow> (\<forall>(x :: vertex) (dx :: int). path src x dx \<longrightarrow> dx < mixfix_lbrb d2 m \<longrightarrow> x |\<in>| to_fset visited2))))))) else (\<forall>(v1 :: vertex). v1 |\<in>| to_fset visited1 \<longrightarrow> shortest_path src v1 (mixfix_lbrb d1 v1)) \<and> (\<forall>(v1 :: vertex). \<not>v1 |\<in>| to_fset visited1 \<longrightarrow> (\<forall>(dv :: int). \<not>path src v1 dv)))"
  sorry
end
